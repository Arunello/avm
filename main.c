// clang main.c -o main
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_DIFFERENCE 0.20

/* Максимальная длина одной строки в check.txt */
#define MAX_LINE 4096

/* Одно слово, найденное в checked.txt */
struct Word {
    long byte_start;
    int byte_len;
    long char_pos;
    int char_len;
};

int utf8_next(const unsigned char *s, int *cp) {
    unsigned char c0 = s[0];
    if (c0 < 0x80) {
        *cp = c0;
        return 1;
    } else if ((c0 & 0xE0) == 0xC0) {
        *cp = ((c0 & 0x1F) << 6) | (s[1] & 0x3F);
        return 2;
    } else if ((c0 & 0xF0) == 0xE0) {
        *cp = ((c0 & 0x0F) << 12) | ((s[1] & 0x3F) << 6) | (s[2] & 0x3F);
        return 3;
    } else if ((c0 & 0xF8) == 0xF0) {
        *cp = ((c0 & 0x07) << 18) | ((s[1] & 0x3F) << 12) | ((s[2] & 0x3F) << 6) | (s[3] & 0x3F);
        return 4;
    } else {
        *cp = c0;
        return 1;
    }
}


int to_lower_cp(int cp) {
    if (cp >= 'A' && cp <= 'Z') return cp + 32;
    if (cp == 0x0401) return 0x0451;                     // Ё -> ё
    if (cp >= 0x0410 && cp <= 0x042F) return cp + 0x20;  // А-Я -> а-я
    return cp;
}

int decode_lower_word(const unsigned char *bytes, int byte_len, int *out_cp) {
    int n = 0, i = 0;
    while (i < byte_len) {
        int cp, clen = utf8_next(bytes + i, &cp);
        out_cp[n++] = to_lower_cp(cp);
        i += clen;
    }
    return n;
}

int damerau_levenshtein(const int *a, int len1, const int *b, int len2) {
    int **d = malloc((size_t)(len1 + 1) * sizeof(int *));
    for (int i = 0; i <= len1; i++) {
        d[i] = malloc((size_t)(len2 + 1) * sizeof(int));
    }

    for (int i = 0; i <= len1; i++) d[i][0] = i;
    for (int j = 0; j <= len2; j++) d[0][j] = j;

    for (int i = 1; i <= len1; i++) {
        for (int j = 1; j <= len2; j++) {
            int cost = (a[i - 1] == b[j - 1]) ? 0 : 1;

            int deletion     = d[i - 1][j] + 1;
            int insertion    = d[i][j - 1] + 1;
            int substitution = d[i - 1][j - 1] + cost;

            int best = deletion;
            if (insertion < best) best = insertion;
            if (substitution < best) best = substitution;

            if (i > 1 && j > 1 && a[i - 1] == b[j - 2] && a[i - 2] == b[j - 1]) {
                int transposition = d[i - 2][j - 2] + 1;
                if (transposition < best) best = transposition;
            }

            d[i][j] = best;
        }
    }

    int result = d[len1][len2];
    for (int i = 0; i <= len1; i++) free(d[i]);
    free(d);
    return result;
}

double calculate_difference(int distance, int len1, int len2) {
    int maxlen = (len1 > len2) ? len1 : len2;
    if (maxlen == 0) return 0.0;
    return (double)distance / (double)maxlen;
}

/* ------------- Чтение checked.txt и разбиение на слова ------------- */

unsigned char *read_whole_file(const char *filename, long *out_size) {
    FILE *f = fopen(filename, "rb");
    if (!f) return NULL;

    fseek(f, 0, SEEK_END);
    long size = ftell(f);
    fseek(f, 0, SEEK_SET);

    /* +4 байта запаса, чтобы utf8_next не вышел за пределы буфера,
     * если последний символ файла окажется повреждённым */
    unsigned char *buf = malloc((size_t)size + 4);
    if (!buf) { fclose(f); return NULL; }

    size_t read_bytes = fread(buf, 1, (size_t)size, f);
    fclose(f);

    buf[read_bytes] = buf[read_bytes + 1] = buf[read_bytes + 2] = buf[read_bytes + 3] = 0;
    *out_size = (long)read_bytes;
    return buf;
}

int is_separator(int cp) {
    return cp == ' ' || cp == '\t' || cp == '\n' || cp == '\r';
}

/* Разбивает буфер checked.txt на слова. Разделителем является
 * пробел, символ табуляции и символы конца строки \n, \r.
 * Массив найденных слов возвращается через out_words/out_count и
 * при необходимости растёт с помощью realloc. */
void tokenize(const unsigned char *buf, long len, struct Word **out_words, int *out_count) {
    int capacity = 64;
    int count = 0;
    struct Word *words = malloc((size_t)capacity * sizeof(struct Word));
    if (!words) { fprintf(stderr, "malloc failed\n"); exit(1); }

    long byte_pos = 0;
    long char_pos = 1;

    while (byte_pos < len) {
        int cp;
        int clen = utf8_next(buf + byte_pos, &cp);

        if (is_separator(cp)) {
            byte_pos += clen;
            char_pos++;
            continue;
        }

        /* начало нового слова */
        long word_byte_start = byte_pos;
        long word_char_pos = char_pos;
        int word_char_len = 0;

        while (byte_pos < len) {
            int wcp;
            int wclen = utf8_next(buf + byte_pos, &wcp);
            if (is_separator(wcp)) break;
            byte_pos += wclen;
            char_pos++;
            word_char_len++;
        }

        if (count == capacity) {
            capacity *= 2;
            struct Word *tmp = realloc(words, (size_t)capacity * sizeof(struct Word));
            if (!tmp) { fprintf(stderr, "realloc failed\n"); free(words); exit(1); }
            words = tmp;
        }

        words[count].byte_start = word_byte_start;
        words[count].byte_len   = (int)(byte_pos - word_byte_start);
        words[count].char_pos   = word_char_pos;
        words[count].char_len   = word_char_len;
        count++;
    }

    *out_words = words;
    *out_count = count;
}

/* ------------- Форматирование разницы вида "16,67%" ------------- */

void format_percent(double diff, char *out, size_t out_size) {
    snprintf(out, out_size, "%.2f%%", diff * 100.0);
    for (char *p = out; *p; p++) {
        if (*p == '.') { *p = ','; break; }
    }
}

/* -------------------------------- main -------------------------------- */

int main() {
    long checked_len;
    unsigned char *checked_buf = read_whole_file("checked.txt", &checked_len);
    if (!checked_buf) {
        fprintf(stderr, "Не удалось открыть checked.txt\n");
        return 1;
    }

    struct Word *words;
    int word_count;
    tokenize(checked_buf, checked_len, &words, &word_count);

    FILE *fcheck = fopen("check.txt", "r");
    if (!fcheck) {
        fprintf(stderr, "Не удалось открыть check.txt\n");
        free(checked_buf);
        free(words);
        return 1;
    }

    FILE *fresult = fopen("result.txt", "w");
    if (!fresult) {
        fprintf(stderr, "Не удалось создать result.txt\n");
        fclose(fcheck);
        free(checked_buf);
        free(words);
        return 1;
    }

    char line[MAX_LINE];
    while (fgets(line, sizeof(line), fcheck)) {
        /* убираем \n и \r в конце строки */
        size_t len = strlen(line);
        while (len > 0 && (line[len - 1] == '\n' || line[len - 1] == '\r')) {
            line[--len] = '\0';
        }
        if (len == 0) continue; /* пустые строки игнорируем */

        fprintf(fresult, "Reference word: \"%s\"\n", line);

        int *ref_cp = malloc(len * sizeof(int));
        if (!ref_cp) { fprintf(stderr, "malloc failed\n"); return 1; }
        int ref_len = decode_lower_word((unsigned char *)line, (int)len, ref_cp);

        int found = 0;
        for (int i = 0; i < word_count; i++) {
            struct Word w = words[i];

            int *cand_cp = malloc((size_t)w.byte_len * sizeof(int));
            if (!cand_cp) { fprintf(stderr, "malloc failed\n"); return 1; }
            int cand_len = decode_lower_word(checked_buf + w.byte_start, w.byte_len, cand_cp);

            int dist = damerau_levenshtein(ref_cp, ref_len, cand_cp, cand_len);
            double diff = calculate_difference(dist, ref_len, cand_len);
            free(cand_cp);

            if (diff <= MAX_DIFFERENCE) {
                const char *type = (dist == 0) ? "full" : "partial";
                char percent_str[32];
                format_percent(diff, percent_str, sizeof(percent_str));

                fprintf(fresult,
                        "  match=\"%.*s\"  position=%ld  length=%d  type=%-7s  difference=%s\n",
                        w.byte_len, (const char *)(checked_buf + w.byte_start),
                        w.char_pos, w.char_len, type, percent_str);
                found = 1;
            }
        }

        if (!found) {
            fprintf(fresult, "  (no matches)\n");
        }
        fprintf(fresult, "\n");

        free(ref_cp);
    }

    fclose(fcheck);
    fclose(fresult);
    free(checked_buf);
    free(words);

    return 0;
}
