#define _POSIX_C_SOURCE 200809L
#define _XOPEN_SOURCE 700

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>   /* strcasecmp */
#include <errno.h>
#include <locale.h>
#include <langinfo.h>  /* nl_langinfo, CODESET */
#include <wchar.h>
#include <wctype.h>

/* Partial-match threshold: difference = DL distance / max(len1, len2). */
static const double PARTIAL_THRESHOLD = 0.20;

/* ------------------------------------------------------------------- */
/* Data structures                                                      */
/* ------------------------------------------------------------------- */

struct Word {
    wchar_t *original;  /* original casing, for output                */
    wchar_t *lowered;   /* lowercased copy, for comparison             */
    size_t   length;    /* length in code points                      */
    size_t   position;  /* 1-based code-point position in source file */
};

struct WordList {
    struct Word *items;
    size_t       count;
    size_t       capacity;
};

struct Match {
    const struct Word *target_word;
    int                is_full;     /* 1 = full match, 0 = partial */
    double             difference;  /* fraction in [0, PARTIAL_THRESHOLD] */
};

/* ------------------------------------------------------------------- */
/* Prototypes                                                           */
/* ------------------------------------------------------------------- */

static int    read_file_bytes(const char *path, unsigned char **out_buf, size_t *out_len);
static size_t utf8_decode_buffer(const unsigned char *buf, size_t len, wchar_t **out_cps);
static int    write_utf8(FILE *out, const wchar_t *s, size_t len);

static int    word_list_push(struct WordList *list, const wchar_t *orig_start,
                              size_t len, size_t position);
static int    build_word_list_from_codepoints(const wchar_t *cps, size_t n_cps,
                                               struct WordList *out);
static int    read_utf8_words(const char *path, struct WordList *out);
static void   free_word_list(struct WordList *list);

static void   check_locale_and_warn(void);
static int    words_equal(const wchar_t *a, const wchar_t *b, size_t len);
static size_t damerau_levenshtein(const wchar_t *a, size_t la,
                                   const wchar_t *b, size_t lb);

static int    write_spaces(FILE *out, size_t n);
static int    collect_matches(const struct Word *rw, const struct WordList *target,
                               struct Match **out_matches, size_t *out_count);
static int    print_block(FILE *out, const struct Word *rw,
                           const struct Match *matches, size_t mcount);
static int    write_results(FILE *out, const struct WordList *ref,
                             const struct WordList *target);

int main(void);

/* ------------------------------------------------------------------- */
/* File reading                                                         */
/* ------------------------------------------------------------------- */

/* Reads the whole contents of `path` into a freshly malloc'd buffer.
 * Works for files of any size without assuming they are seekable. */
static int read_file_bytes(const char *path, unsigned char **out_buf, size_t *out_len) {
    FILE *f = fopen(path, "rb");
    if (f == NULL) {
        fprintf(stderr, "error: cannot open '%s': %s\n", path, strerror(errno));
        return -1;
    }

    size_t cap = 65536;
    size_t len = 0;
    unsigned char *buf = malloc(cap);
    if (buf == NULL) {
        fprintf(stderr, "error: out of memory reading '%s'\n", path);
        fclose(f);
        return -1;
    }

    for (;;) {
        if (len == cap) {
            size_t newcap = cap * 2;
            unsigned char *tmp = realloc(buf, newcap);
            if (tmp == NULL) {
                fprintf(stderr, "error: out of memory reading '%s'\n", path);
                free(buf);
                fclose(f);
                return -1;
            }
            buf = tmp;
            cap = newcap;
        }
        size_t want = cap - len;
        size_t got = fread(buf + len, 1, want, f);
        len += got;
        if (got < want) {
            if (ferror(f)) {
                fprintf(stderr, "error: read error on '%s': %s\n", path, strerror(errno));
                free(buf);
                fclose(f);
                return -1;
            }
            break; /* EOF reached */
        }
    }

    if (fclose(f) != 0) {
        fprintf(stderr, "error: failed to close '%s': %s\n", path, strerror(errno));
        free(buf);
        return -1;
    }

    *out_buf = buf;
    *out_len = len;
    return 0;
}

/* ------------------------------------------------------------------- */
/* UTF-8 decoding / encoding                                            */
/* ------------------------------------------------------------------- */

/* Decodes a raw UTF-8 byte buffer into an array of Unicode code points
 * (stored as wchar_t, which is a 32-bit type on both FreeBSD and Linux).
 * Any malformed byte (invalid lead byte, truncated sequence, bad
 * continuation byte, overlong encoding, surrogate half, or code point
 * above U+10FFFF) is replaced with a single U+FFFD REPLACEMENT CHARACTER
 * and decoding resumes at the very next byte -- this routine never fails
 * or aborts on malformed input, it only substitutes/resyncs.
 *
 * This is a self-contained decoder (rather than mbrtowc()) so that
 * decoding is correct regardless of which locales are installed/active
 * on the machine running the program.
 *
 * On success returns the number of decoded code points and sets
 * *out_cps to a malloc'd array (which may be NULL when the count is 0).
 * Returns (size_t)-1 on allocation failure.
 */
static size_t utf8_decode_buffer(const unsigned char *buf, size_t len, wchar_t **out_cps) {
    wchar_t *cps = NULL;
    size_t cap = 0, n = 0;
    size_t i = 0;

    while (i < len) {
        unsigned char b0 = buf[i];
        unsigned long cp = 0xFFFDUL;
        size_t seqlen = 1;
        int valid = 1;

        if (b0 < 0x80) {
            cp = b0;
            seqlen = 1;
        } else if ((b0 & 0xE0) == 0xC0) {
            cp = (unsigned long)(b0 & 0x1F);
            seqlen = 2;
        } else if ((b0 & 0xF0) == 0xE0) {
            cp = (unsigned long)(b0 & 0x0F);
            seqlen = 3;
        } else if ((b0 & 0xF8) == 0xF0) {
            cp = (unsigned long)(b0 & 0x07);
            seqlen = 4;
        } else {
            valid = 0;
        }

        if (valid && seqlen > 1) {
            if (i + seqlen > len) {
                valid = 0; /* truncated at end of file */
            } else {
                size_t k;
                for (k = 1; k < seqlen; k++) {
                    unsigned char bc = buf[i + k];
                    if ((bc & 0xC0) != 0x80) { valid = 0; break; }
                    cp = (cp << 6) | (unsigned long)(bc & 0x3F);
                }
            }
        }

        if (valid) {
            /* Reject overlong encodings, surrogate halves, and values
             * outside the valid Unicode range. */
            if (seqlen == 2 && cp < 0x80) valid = 0;
            else if (seqlen == 3 && cp < 0x800) valid = 0;
            else if (seqlen == 4 && cp < 0x10000) valid = 0;
            else if (cp > 0x10FFFFUL) valid = 0;
            else if (cp >= 0xD800UL && cp <= 0xDFFFUL) valid = 0;
        }

        if (!valid) {
            cp = 0xFFFDUL;
            seqlen = 1; /* consume exactly one byte, then resynchronize */
        }

        if (n == cap) {
            size_t newcap = (cap == 0) ? 256 : cap * 2;
            wchar_t *tmp = realloc(cps, newcap * sizeof(wchar_t));
            if (tmp == NULL) {
                free(cps);
                return (size_t)-1;
            }
            cps = tmp;
            cap = newcap;
        }
        cps[n++] = (wchar_t)cp;
        i += seqlen;
    }

    *out_cps = cps;
    return n;
}

/* Encodes `len` code points from `s` to UTF-8 bytes and writes them to
 * `out`. Symmetric, locale-independent counterpart of utf8_decode_buffer().
 * Returns 0 on success, -1 on a write error. */
static int write_utf8(FILE *out, const wchar_t *s, size_t len) {
    size_t i;
    for (i = 0; i < len; i++) {
        unsigned long cp = (unsigned long)s[i];
        unsigned char buf[4];
        size_t n;

        if (cp < 0x80UL) {
            buf[0] = (unsigned char)cp;
            n = 1;
        } else if (cp < 0x800UL) {
            buf[0] = (unsigned char)(0xC0 | (cp >> 6));
            buf[1] = (unsigned char)(0x80 | (cp & 0x3F));
            n = 2;
        } else if (cp < 0x10000UL) {
            buf[0] = (unsigned char)(0xE0 | (cp >> 12));
            buf[1] = (unsigned char)(0x80 | ((cp >> 6) & 0x3F));
            buf[2] = (unsigned char)(0x80 | (cp & 0x3F));
            n = 3;
        } else {
            buf[0] = (unsigned char)(0xF0 | (cp >> 18));
            buf[1] = (unsigned char)(0x80 | ((cp >> 12) & 0x3F));
            buf[2] = (unsigned char)(0x80 | ((cp >> 6) & 0x3F));
            buf[3] = (unsigned char)(0x80 | (cp & 0x3F));
            n = 4;
        }
        if (fwrite(buf, 1, n, out) != n) return -1;
    }
    return 0;
}

/* ------------------------------------------------------------------- */
/* Word-list construction                                               */
/* ------------------------------------------------------------------- */

static int word_list_push(struct WordList *list, const wchar_t *orig_start,
                           size_t len, size_t position) {
    if (list->count == list->capacity) {
        size_t newcap = (list->capacity == 0) ? 16 : list->capacity * 2;
        struct Word *tmp = realloc(list->items, newcap * sizeof(struct Word));
        if (tmp == NULL) return -1;
        list->items = tmp;
        list->capacity = newcap;
    }

    wchar_t *orig = malloc((len + 1) * sizeof(wchar_t));
    if (orig == NULL) return -1;
    wchar_t *low = malloc((len + 1) * sizeof(wchar_t));
    if (low == NULL) { free(orig); return -1; }

    size_t k;
    for (k = 0; k < len; k++) {
        orig[k] = orig_start[k];
        low[k] = (wchar_t)towlower((wint_t)orig_start[k]);
    }
    orig[len] = L'\0';
    low[len] = L'\0';

    struct Word *w = &list->items[list->count];
    w->original = orig;
    w->lowered = low;
    w->length = len;
    w->position = position;
    list->count++;
    return 0;
}

/* Splits a sequence of decoded code points into whitespace-separated
 * words, recording each word's original text, lowercased text, length,
 * and 1-based starting position (counted in code points from the very
 * start of the sequence, exactly as required -- every code point,
 * including whitespace and newlines, advances the position count since
 * `cps` already contains every decoded code point of the file in order). */
static int build_word_list_from_codepoints(const wchar_t *cps, size_t n_cps,
                                            struct WordList *out) {
    out->items = NULL;
    out->count = 0;
    out->capacity = 0;

    size_t i = 0;
    while (i < n_cps) {
        while (i < n_cps && iswspace((wint_t)cps[i])) i++;
        if (i >= n_cps) break;

        size_t start = i;
        while (i < n_cps && !iswspace((wint_t)cps[i])) i++;
        size_t wlen = i - start;
        size_t position = start + 1; /* 1-based */

        if (word_list_push(out, &cps[start], wlen, position) != 0) {
            return -1;
        }
    }
    return 0;
}

static int read_utf8_words(const char *path, struct WordList *out) {
    unsigned char *buf = NULL;
    size_t len = 0;
    if (read_file_bytes(path, &buf, &len) != 0) {
        return -1; /* message already printed */
    }

    wchar_t *cps = NULL;
    size_t n_cps = utf8_decode_buffer(buf, len, &cps);
    free(buf);
    if (n_cps == (size_t)-1) {
        fprintf(stderr, "error: out of memory while decoding UTF-8 in '%s'\n", path);
        return -1;
    }

    int rc = build_word_list_from_codepoints(cps, n_cps, out);
    free(cps);
    if (rc != 0) {
        fprintf(stderr, "error: out of memory while parsing words in '%s'\n", path);
        return -1;
    }
    return 0;
}

static void free_word_list(struct WordList *list) {
    if (list == NULL) return;
    size_t i;
    for (i = 0; i < list->count; i++) {
        free(list->items[i].original);
        free(list->items[i].lowered);
    }
    free(list->items);
    list->items = NULL;
    list->count = 0;
    list->capacity = 0;
}

/* ------------------------------------------------------------------- */
/* Locale                                                               */
/* ------------------------------------------------------------------- */

/* Sets the locale from the environment and warns (without ever aborting)
 * if it does not appear to be UTF-8. File decoding/encoding is done by
 * hand elsewhere and is unaffected either way; only towlower()'s
 * handling of non-ASCII letters depends on this. */
static void check_locale_and_warn(void) {
    const char *loc = setlocale(LC_ALL, "");
    if (loc == NULL) {
        fprintf(stderr,
                "warning: could not set locale from the environment; "
                "case-insensitive comparison of non-ASCII letters may be "
                "inaccurate (UTF-8 file reading/writing is unaffected).\n");
        return;
    }

    char *codeset = nl_langinfo(CODESET);
    int is_utf8 = 0;
    if (codeset != NULL &&
        (strcasecmp(codeset, "UTF-8") == 0 || strcasecmp(codeset, "UTF8") == 0)) {
        is_utf8 = 1;
    }
    if (!is_utf8 && MB_CUR_MAX >= 4) {
        is_utf8 = 1;
    }
    if (!is_utf8) {
        fprintf(stderr,
                "warning: locale '%s' does not appear to use a UTF-8 codeset "
                "(codeset=%s); case-insensitive comparison of non-ASCII "
                "letters may be inaccurate. UTF-8 file reading/writing is "
                "performed internally by this program and is unaffected.\n",
                loc, codeset != NULL ? codeset : "unknown");
    }
}

/* ------------------------------------------------------------------- */
/* Word comparison                                                      */
/* ------------------------------------------------------------------- */

static int words_equal(const wchar_t *a, const wchar_t *b, size_t len) {
    size_t i;
    for (i = 0; i < len; i++) {
        if (a[i] != b[i]) return 0;
    }
    return 1;
}

/*
 * True (unrestricted) Damerau-Levenshtein distance between two code-point
 * arrays, computed with the classic Lowrance-Wagner O(n*m) dynamic
 * programming algorithm. This counts an adjacent transposition as a
 * single edit even when the transposed characters recur later in the
 * strings, unlike the simpler "optimal string alignment" (OSA) distance,
 * which is NOT what is implemented here.
 *
 * `da` records, for each distinct character seen so far in `a`, the most
 * recent row at which it occurred (0 = not yet seen) -- exactly the "da"
 * array of the reference algorithm. A small linear-scan association list
 * is used instead of an array indexed directly by code point (which could
 * demand a huge allocation for a single high-value Unicode character);
 * this is efficient enough for the short words this program deals with.
 *
 * Returns (size_t)-1 if memory allocation fails.
 */
static size_t damerau_levenshtein(const wchar_t *a, size_t la,
                                   const wchar_t *b, size_t lb) {
    if (la == 0) return lb;
    if (lb == 0) return la;

    long n = (long)la;
    long m = (long)lb;
    long maxdist = n + m;

    size_t cols = (size_t)m + 2;
    size_t rows = (size_t)n + 2;
    size_t *d = malloc(rows * cols * sizeof(size_t));
    if (d == NULL) return (size_t)-1;

    /* d[] holds logical indices -1..n by -1..m, shifted by +1 for storage. */
#define D(i, j) d[(size_t)((i) + 1) * cols + (size_t)((j) + 1)]

    D(-1, -1) = (size_t)maxdist;
    {
        long p;
        for (p = 0; p <= n; p++) {
            D(p, -1) = (size_t)maxdist;
            D(p, 0) = (size_t)p;
        }
    }
    {
        long q;
        for (q = 0; q <= m; q++) {
            D(-1, q) = (size_t)maxdist;
            D(0, q) = (size_t)q;
        }
    }

    struct { wchar_t ch; long row; } *da = NULL;
    size_t da_count = 0, da_cap = 0;
    long i;

    for (i = 1; i <= n; i++) {
        long db = 0;
        long j;
        for (j = 1; j <= m; j++) {
            long k = 0;
            size_t s;
            for (s = 0; s < da_count; s++) {
                if (da[s].ch == b[j - 1]) { k = da[s].row; break; }
            }
            long l = db;
            size_t cost;

            if (a[i - 1] == b[j - 1]) {
                cost = 0;
                db = j;
            } else {
                cost = 1;
            }

            size_t sub = D(i - 1, j - 1) + cost;
            size_t ins = D(i, j - 1) + 1;
            size_t del = D(i - 1, j) + 1;
            size_t best = sub;
            if (ins < best) best = ins;
            if (del < best) best = del;

            {
                size_t trans = D(k - 1, l - 1)
                             + (size_t)(i - k - 1) + 1 + (size_t)(j - l - 1);
                if (trans < best) best = trans;
            }

            D(i, j) = best;
        }

        {
            int found = 0;
            size_t s;
            for (s = 0; s < da_count; s++) {
                if (da[s].ch == a[i - 1]) { da[s].row = i; found = 1; break; }
            }
            if (!found) {
                if (da_count == da_cap) {
                    size_t newcap = (da_cap == 0) ? 16 : da_cap * 2;
                    void *tmp = realloc(da, newcap * sizeof(*da));
                    if (tmp == NULL) { free(d); free(da); return (size_t)-1; }
                    da = tmp;
                    da_cap = newcap;
                }
                da[da_count].ch = a[i - 1];
                da[da_count].row = i;
                da_count++;
            }
        }
    }

    size_t result = D(n, m);
    free(d);
    free(da);
#undef D
    return result;
}

/* ------------------------------------------------------------------- */
/* Matching and output                                                  */
/* ------------------------------------------------------------------- */

static int write_spaces(FILE *out, size_t n) {
    size_t i;
    for (i = 0; i < n; i++) {
        if (fputc(' ', out) == EOF) return -1;
    }
    return 0;
}

/* Scans every word of `target` for full/partial matches against `rw` and
 * appends them, in ascending target-position order (which is simply the
 * order `target` was built in), to a freshly allocated array.
 * Returns 0 on success (with *out_count possibly 0) or -1 on OOM. */
static int collect_matches(const struct Word *rw, const struct WordList *target,
                            struct Match **out_matches, size_t *out_count) {
    struct Match *matches = NULL;
    size_t count = 0, cap = 0;
    size_t t;

    for (t = 0; t < target->count; t++) {
        const struct Word *tw = &target->items[t];
        size_t maxlen = (rw->length > tw->length) ? rw->length : tw->length;
        if (maxlen == 0) continue; /* defensive; words are never empty */

        int is_full = (rw->length == tw->length) &&
                      words_equal(rw->lowered, tw->lowered, rw->length);
        double difference = 0.0;

        if (!is_full) {
            size_t lendiff = (rw->length > tw->length)
                            ? (rw->length - tw->length)
                            : (tw->length - rw->length);
            /* The edit distance can never be smaller than the difference
             * in length, so the expensive DP can be skipped whenever that
             * alone already exceeds the threshold. */
            if ((double)lendiff / (double)maxlen > PARTIAL_THRESHOLD) {
                continue;
            }
            size_t dist = damerau_levenshtein(rw->lowered, rw->length,
                                               tw->lowered, tw->length);
            if (dist == (size_t)-1) {
                free(matches);
                return -1;
            }
            difference = (double)dist / (double)maxlen;
            if (difference > PARTIAL_THRESHOLD) {
                continue;
            }
        }

        if (count == cap) {
            size_t newcap = (cap == 0) ? 8 : cap * 2;
            struct Match *tmp = realloc(matches, newcap * sizeof(struct Match));
            if (tmp == NULL) { free(matches); return -1; }
            matches = tmp;
            cap = newcap;
        }
        matches[count].target_word = tw;
        matches[count].is_full = is_full;
        matches[count].difference = difference;
        count++;
    }

    *out_matches = matches;
    *out_count = count;
    return 0;
}

/* Writes one "Reference word: ..." block, with its match lines (or the
 * "(no matches)" line) aligned into columns. Column widths are computed
 * per-block as (the widest field text among this block's matches) + 2. */
static int print_block(FILE *out, const struct Word *rw,
                        const struct Match *matches, size_t mcount) {
    if (fputs("Reference word: \"", out) == EOF) return -1;
    if (write_utf8(out, rw->original, rw->length) != 0) return -1;
    if (fputs("\"\n", out) == EOF) return -1;

    if (mcount == 0) {
        if (fputs("  (no matches)\n", out) == EOF) return -1;
        return 0;
    }

    char (*pos_s)[32]  = malloc(mcount * sizeof *pos_s);
    char (*len_s)[32]  = malloc(mcount * sizeof *len_s);
    char (*type_s)[16] = malloc(mcount * sizeof *type_s);
    char (*diff_s)[32] = malloc(mcount * sizeof *diff_s);
    if (pos_s == NULL || len_s == NULL || type_s == NULL || diff_s == NULL) {
        free(pos_s); free(len_s); free(type_s); free(diff_s);
        return -1;
    }

    size_t w_match = 0, w_pos = 0, w_len = 0, w_type = 0;
    size_t i;
    for (i = 0; i < mcount; i++) {
        const struct Word *tw = matches[i].target_word;
        size_t match_w = 8 + tw->length; /* "match=\"" + word + "\"" */
        if (match_w > w_match) w_match = match_w;

        int n = snprintf(pos_s[i], sizeof pos_s[i], "position=%zu", tw->position);
        if (n < 0) { free(pos_s); free(len_s); free(type_s); free(diff_s); return -1; }
        if ((size_t)n > w_pos) w_pos = (size_t)n;

        n = snprintf(len_s[i], sizeof len_s[i], "length=%zu", tw->length);
        if (n < 0) { free(pos_s); free(len_s); free(type_s); free(diff_s); return -1; }
        if ((size_t)n > w_len) w_len = (size_t)n;

        n = snprintf(type_s[i], sizeof type_s[i], "type=%s",
                     matches[i].is_full ? "full" : "partial");
        if (n < 0) { free(pos_s); free(len_s); free(type_s); free(diff_s); return -1; }
        if ((size_t)n > w_type) w_type = (size_t)n;

        n = snprintf(diff_s[i], sizeof diff_s[i], "difference=%.2f%%",
                     matches[i].difference * 100.0);
        if (n < 0) { free(pos_s); free(len_s); free(type_s); free(diff_s); return -1; }
    }

    size_t col_match = w_match + 2;
    size_t col_pos   = w_pos + 2;
    size_t col_len   = w_len + 2;
    size_t col_type  = w_type + 2;

    int err = 0;
    for (i = 0; i < mcount && !err; i++) {
        const struct Word *tw = matches[i].target_word;
        size_t used;

        if (!err && fputs("  match=\"", out) == EOF) err = 1;
        if (!err && write_utf8(out, tw->original, tw->length) != 0) err = 1;
        if (!err && fputc('"', out) == EOF) err = 1;
        used = 8 + tw->length;
        if (!err && write_spaces(out, col_match - used) != 0) err = 1;

        if (!err && fputs(pos_s[i], out) == EOF) err = 1;
        if (!err && write_spaces(out, col_pos - strlen(pos_s[i])) != 0) err = 1;

        if (!err && fputs(len_s[i], out) == EOF) err = 1;
        if (!err && write_spaces(out, col_len - strlen(len_s[i])) != 0) err = 1;

        if (!err && fputs(type_s[i], out) == EOF) err = 1;
        if (!err && write_spaces(out, col_type - strlen(type_s[i])) != 0) err = 1;

        if (!err && fputs(diff_s[i], out) == EOF) err = 1;
        if (!err && fputc('\n', out) == EOF) err = 1;
    }

    free(pos_s); free(len_s); free(type_s); free(diff_s);
    return err ? -1 : 0;
}

static int write_results(FILE *out, const struct WordList *ref,
                          const struct WordList *target) {
    size_t r;
    for (r = 0; r < ref->count; r++) {
        const struct Word *rw = &ref->items[r];
        struct Match *matches = NULL;
        size_t mcount = 0;

        if (collect_matches(rw, target, &matches, &mcount) != 0) {
            fprintf(stderr, "error: out of memory while matching reference word %zu\n", r + 1);
            return -1;
        }

        if (r > 0) {
            if (fputc('\n', out) == EOF) {
                free(matches);
                fprintf(stderr, "error: write failure on 'result.txt'\n");
                return -1;
            }
        }

        if (print_block(out, rw, matches, mcount) != 0) {
            free(matches);
            fprintf(stderr, "error: write failure on 'result.txt'\n");
            return -1;
        }

        free(matches);
    }
    return 0;
}

/* ------------------------------------------------------------------- */
/* main                                                                  */
/* ------------------------------------------------------------------- */

int main(void) {
    check_locale_and_warn();

    struct WordList ref = { NULL, 0, 0 };
    struct WordList target = { NULL, 0, 0 };
    int status = EXIT_SUCCESS;

    if (read_utf8_words("check", &ref) != 0) {
        free_word_list(&ref);
        return EXIT_FAILURE;
    }

    if (read_utf8_words("checked", &target) != 0) {
        free_word_list(&ref);
        free_word_list(&target);
        return EXIT_FAILURE;
    }

    FILE *out = fopen("result.txt", "w");
    if (out == NULL) {
        fprintf(stderr, "error: cannot open 'result.txt' for writing: %s\n", strerror(errno));
        free_word_list(&ref);
        free_word_list(&target);
        return EXIT_FAILURE;
    }

    if (write_results(out, &ref, &target) != 0) {
        status = EXIT_FAILURE;
    }

    if (fclose(out) != 0) {
        if (status == EXIT_SUCCESS) {
            fprintf(stderr, "error: failed to close 'result.txt': %s\n", strerror(errno));
        }
        status = EXIT_FAILURE;
    }

    free_word_list(&ref);
    free_word_list(&target);

    return status;
}
