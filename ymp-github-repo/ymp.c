/*
 * ymp.c - минимальный клиент Яндекс Музыки для Windows Mobile 6 (ARM)
 * Сборка: см. build.sh (cegcc + mbedTLS 2.28 LTS + minimp3.h)
 *
 * Что делает:
 *   - TLS 1.2 через mbedTLS (системный schannel на WM6 его не умеет)
 *   - берёт список "Мне нравится", "Мою волну", поиск, текст песен (Яндекс, запасной - lrclib.net)
 *   - по тапу: get-file-info -> скачивание -> AES-CTR расшифровка -> minimp3 -> waveOut
 */
#define UNICODE
#define _UNICODE
#include <windows.h>
#include <winsock2.h>
#include <mmsystem.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <time.h>

#include "mbedtls/ssl.h"
#include "mbedtls/entropy.h"
#include "mbedtls/ctr_drbg.h"
#include "mbedtls/aes.h"
#include "mbedtls/md.h"
#include "mbedtls/base64.h"

#define MINIMP3_IMPLEMENTATION
#define MINIMP3_ONLY_MP3
#define MINIMP3_NO_SIMD
#include "minimp3.h"

#define STB_IMAGE_IMPLEMENTATION
#define STBI_ONLY_JPEG
#define STBI_NO_STDIO
#define STBI_NO_HDR
#define STBI_NO_LINEAR
#define STBI_NO_SIMD
#define STBI_NO_THREAD_LOCALS
#define STBI_NO_FAILURE_STRINGS
#include "stb_image.h"

/* ---------------------------------------------------------------- config */
static char C_token[256], C_hmac[64];
static char C_dclient[64] = "YandexMusicDesktopAppWindows/5.95.0";
static char C_host[64]    = "api.music.yandex.net";
static char C_quality[8]  = "nq";          /* lq / nq */
static int  C_count       = 40;            /* сколько лайкнутых треков грузить */
static int  C_autowave    = 1;             /* 1 = при запуске сразу включать "Мою волну" */

#define MAXT 300   /* размер очереди (волна дозагружается порциями) */
#define MAXL 100   /* максимум лайкнутых треков */
static char g_ids[MAXT][24];
static int  g_nt;

static HWND g_hwnd, g_list, g_stat;

static char g_uid[32];
static WCHAR g_ttl[MAXT][96], g_art[MAXT][64];
static volatile int g_liked[MAXT];
static volatile long g_clen, g_elapsed_ms, g_total_s;
static volatile int g_repeat, g_active;
static char g_cover[MAXT][128];
static volatile int g_coverIdx = -1;
static HBITMAP g_hCover; static int g_coverW, g_coverH;
static char g_login[48], g_name[64], g_rsid[96], g_batch[96];
static WCHAR g_wName[64], g_wLogin[48];
static volatile int g_plus, g_mode, g_morebusy, g_nlikes, g_saved;
static volatile int g_lyr[MAXT];                                  /* у трека есть текст песни */
static volatile long g_range;                                    /* с какого байта качать файл (перемотка) */
static volatile int g_resp_status, g_seek_pm = -1, g_seek_ignored;   /* запрос перемотки в промилле от длины */   /* g_mode: 0 = любимые, 1 = моя волна */
static CRITICAL_SECTION g_cs;

static void status(const char *fmt, ...)
{
    char a[200]; WCHAR w[200]; va_list ap;
    va_start(ap, fmt); _vsnprintf(a, sizeof a - 1, fmt, ap); va_end(ap);
    a[sizeof a - 1] = 0;
    MultiByteToWideChar(CP_UTF8, 0, a, -1, w, 200);
    SetWindowTextW(g_stat, w);
}

/* показывает этап в строке статуса и дописывает его в ymp.log рядом с exe */
static void dbg(const char *fmt, ...)
{
    char a[200]; va_list ap; HANDLE h; DWORD n; WCHAR p[MAX_PATH], *dot;
    va_start(ap, fmt); _vsnprintf(a, sizeof a - 3, fmt, ap); va_end(ap);
    a[sizeof a - 3] = 0;
    status("%s", a);
    GetModuleFileNameW(NULL, p, MAX_PATH);
    dot = wcsrchr(p, L'.'); if (dot) wcscpy(dot, L".log");
    h = CreateFileW(p, GENERIC_WRITE, FILE_SHARE_READ, NULL, OPEN_ALWAYS, 0, NULL);
    if (h != INVALID_HANDLE_VALUE) {
        SetFilePointer(h, 0, NULL, FILE_END);
        strcat(a, "\r\n"); WriteFile(h, a, (DWORD)strlen(a), &n, NULL); CloseHandle(h);
    }
}

/* только в ymp.log (строку статуса не трогает) */
static void logline(const char *fmt, ...)
{
    char a[300]; va_list ap; HANDLE h; DWORD n; WCHAR p[MAX_PATH], *dot;
    va_start(ap, fmt); _vsnprintf(a, sizeof a - 3, fmt, ap); va_end(ap);
    a[sizeof a - 3] = 0; strcat(a, "\r\n");
    GetModuleFileNameW(NULL, p, MAX_PATH);
    dot = wcsrchr(p, L'.'); if (dot) wcscpy(dot, L".log");
    h = CreateFileW(p, GENERIC_WRITE, FILE_SHARE_READ, NULL, OPEN_ALWAYS, 0, NULL);
    if (h != INVALID_HANDLE_VALUE) {
        if (GetFileSize(h, NULL) > 60000) SetEndOfFile(h);   /* лог не растёт бесконечно */
        SetFilePointer(h, 0, NULL, FILE_END); WriteFile(h, a, (DWORD)strlen(a), &n, NULL); CloseHandle(h);
    }
}

static void load_config(void)
{
    WCHAR p[MAX_PATH]; char buf[2048], *line, *nx; DWORD n = 0; HANDLE h; WCHAR *dot;
    GetModuleFileNameW(NULL, p, MAX_PATH);
    dot = wcsrchr(p, L'.'); if (dot) wcscpy(dot, L".ini");
    h = CreateFileW(p, GENERIC_READ, FILE_SHARE_READ, NULL, OPEN_EXISTING, 0, NULL);
    if (h == INVALID_HANDLE_VALUE) return;
    ReadFile(h, buf, sizeof buf - 1, &n, NULL); CloseHandle(h); buf[n] = 0;
    for (line = buf; line && *line; line = nx) {
        char *eq, *e;
        nx = strchr(line, '\n'); if (nx) *nx++ = 0;
        e = line + strlen(line); while (e > line && (e[-1] == '\r' || e[-1] == ' ')) *--e = 0;
        eq = strchr(line, '='); if (!eq) continue; *eq++ = 0;
        if (!strcmp(line, "token"))   strncpy(C_token, eq, sizeof C_token - 1);
        if (!strcmp(line, "hmac"))    strncpy(C_hmac, eq, sizeof C_hmac - 1);
        if (!strcmp(line, "host"))    strncpy(C_host, eq, sizeof C_host - 1);
        if (!strcmp(line, "quality")) strncpy(C_quality, eq, sizeof C_quality - 1);
        if (!strcmp(line, "dclient")) strncpy(C_dclient, eq, sizeof C_dclient - 1);
        if (!strcmp(line, "count"))   C_count = atoi(eq);
        if (!strcmp(line, "autowave")) C_autowave = atoi(eq);
    }
    if (C_count > MAXL) C_count = MAXL;
    if (C_count < 1) C_count = 1;
}

/* ------------------------------------------------------------------ TLS */
extern BOOL WINAPI CeGenRandom(DWORD, BYTE *);

static mbedtls_entropy_context  g_ent;
static mbedtls_ctr_drbg_context g_drbg;
static mbedtls_ssl_config       g_conf;

static int ce_entropy(void *d, unsigned char *out, size_t len, size_t *olen)
{
    (void)d;
    if (!CeGenRandom((DWORD)len, out)) return MBEDTLS_ERR_ENTROPY_SOURCE_FAILED;
    *olen = len; return 0;
}

static int tls_init(void)
{
    WSADATA w; WSAStartup(MAKEWORD(2, 2), &w);
    mbedtls_entropy_init(&g_ent); mbedtls_ctr_drbg_init(&g_drbg); mbedtls_ssl_config_init(&g_conf);
    mbedtls_entropy_add_source(&g_ent, ce_entropy, NULL, 32, MBEDTLS_ENTROPY_SOURCE_STRONG);
    if (mbedtls_ctr_drbg_seed(&g_drbg, mbedtls_entropy_func, &g_ent, (const unsigned char *)"ymp", 3)) return -1;
    if (mbedtls_ssl_config_defaults(&g_conf, MBEDTLS_SSL_IS_CLIENT, MBEDTLS_SSL_TRANSPORT_STREAM,
                                    MBEDTLS_SSL_PRESET_DEFAULT)) return -2;
    /* ВНИМАНИЕ: сертификат сервера НЕ проверяется (экономия места/времени).
       Трафик шифруется, но защиты от MITM нет. См. README. */
    mbedtls_ssl_conf_authmode(&g_conf, MBEDTLS_SSL_VERIFY_NONE);
    mbedtls_ssl_conf_rng(&g_conf, mbedtls_ctr_drbg_random, &g_drbg);
    mbedtls_ssl_conf_min_version(&g_conf, MBEDTLS_SSL_MAJOR_VERSION_3, MBEDTLS_SSL_MINOR_VERSION_3);
    return 0;
}

typedef struct { SOCKET s; mbedtls_ssl_context ssl; } Conn;

static int bio_send(void *c, const unsigned char *b, size_t n)
{ int r = send(*(SOCKET *)c, (const char *)b, (int)n, 0); return r < 0 ? -1 : r; }
static int bio_recv(void *c, unsigned char *b, size_t n)
{ int r = recv(*(SOCKET *)c, (char *)b, (int)n, 0); return r < 0 ? -1 : r; }

static Conn *conn_open(const char *host)
{
    struct hostent *he; struct sockaddr_in a; Conn *c; DWORD to = 20000; int r;
    fd_set wf, ef; struct timeval tv; u_long nb; int verbose = !strcmp(host, C_host);
    if (verbose) dbg("1/3 DNS: %s ...", host);
    he = gethostbyname(host);
    if (!he) { dbg("DNS ошибка %d (нет сети?)", WSAGetLastError()); return 0; }
    if (verbose) dbg("1/3 DNS ok. 2/3 соединение...");
    c = (Conn *)calloc(1, sizeof(Conn));
    c->s = socket(AF_INET, SOCK_STREAM, 0);
    memset(&a, 0, sizeof a); a.sin_family = AF_INET; a.sin_port = htons(443);
    memcpy(&a.sin_addr, he->h_addr_list[0], 4);
    setsockopt(c->s, SOL_SOCKET, SO_RCVTIMEO, (char *)&to, sizeof to);
    setsockopt(c->s, SOL_SOCKET, SO_SNDTIMEO, (char *)&to, sizeof to);
    nb = 1; ioctlsocket(c->s, FIONBIO, &nb);
    connect(c->s, (struct sockaddr *)&a, sizeof a);
    FD_ZERO(&wf); FD_ZERO(&ef); FD_SET(c->s, &wf); FD_SET(c->s, &ef);
    tv.tv_sec = 15; tv.tv_usec = 0;
    r = select(0, NULL, &wf, &ef, &tv);
    if (r <= 0 || FD_ISSET(c->s, &ef)) {
        dbg("Соединение не удалось (%s)", r == 0 ? "таймаут 15с" : "отказ");
        closesocket(c->s); free(c); return 0;
    }
    nb = 0; ioctlsocket(c->s, FIONBIO, &nb);
    if (verbose) dbg("2/3 соединён. 3/3 TLS рукопожатие...");
    mbedtls_ssl_init(&c->ssl);
    if (mbedtls_ssl_setup(&c->ssl, &g_conf) || mbedtls_ssl_set_hostname(&c->ssl, host)) {
        dbg("Ошибка настройки TLS (память?)"); goto fail;
    }
    mbedtls_ssl_set_bio(&c->ssl, &c->s, bio_send, bio_recv, NULL);
    EnterCriticalSection(&g_cs);
    while ((r = mbedtls_ssl_handshake(&c->ssl)) != 0)
        if (r != MBEDTLS_ERR_SSL_WANT_READ && r != MBEDTLS_ERR_SSL_WANT_WRITE) {
            LeaveCriticalSection(&g_cs);
            dbg("TLS ошибка -0x%04X", -r); goto fail;
        }
    LeaveCriticalSection(&g_cs);
    if (verbose) dbg("TLS ok");
    return c;
fail:
    mbedtls_ssl_free(&c->ssl); closesocket(c->s); free(c); return 0;
}

static void conn_close(Conn *c)
{
    mbedtls_ssl_close_notify(&c->ssl); mbedtls_ssl_free(&c->ssl); closesocket(c->s); free(c);
}

static int c_read(Conn *c, unsigned char *b, int n)
{
    int r;
    do r = mbedtls_ssl_read(&c->ssl, b, n);
    while (r == MBEDTLS_ERR_SSL_WANT_READ || r == MBEDTLS_ERR_SSL_WANT_WRITE);
    return r;
}

static int c_write(Conn *c, const char *b, int n)
{
    while (n > 0) {
        int r = mbedtls_ssl_write(&c->ssl, (const unsigned char *)b, n);
        if (r == MBEDTLS_ERR_SSL_WANT_READ || r == MBEDTLS_ERR_SSL_WANT_WRITE) continue;
        if (r <= 0) return -1;
        b += r; n -= r;
    }
    return 0;
}

/* ----------------------------------------------------------------- HTTP */
typedef int (*SinkFn)(const unsigned char *, int, void *);   /* ненулевой возврат = прервать */

typedef struct { int mode; long remain; int st; long csz; int ext; } Body; /* mode 0=до закрытия 1=length 2=chunked */

static int feed(Body *b, const unsigned char *p, int n, SinkFn sink, void *ctx)  /* 1 = конец тела, <0 = abort */
{
    int i = 0;
    if (b->mode == 0) return sink(p, n, ctx) ? -1 : 0;
    if (b->mode == 1) {
        long t = n < b->remain ? n : b->remain;
        if (t && sink(p, (int)t, ctx)) return -1;
        b->remain -= t; return b->remain == 0;
    }
    while (i < n) {
        if (b->st == 0) {
            unsigned char c = p[i++];
            if (c == ';') b->ext = 1;
            else if (c == '\n') {
                b->ext = 0;
                if (b->csz == 0) return 1;
                b->remain = b->csz; b->csz = 0; b->st = 1;
            } else if (!b->ext) {
                int v = (c >= '0' && c <= '9') ? c - '0' : ((c | 32) >= 'a' && (c | 32) <= 'f') ? (c | 32) - 'a' + 10 : -1;
                if (v >= 0) b->csz = b->csz * 16 + v;
            }
        } else if (b->st == 1) {
            long t = n - i < b->remain ? n - i : b->remain;
            if (sink(p + i, (int)t, ctx)) return -1;
            i += (int)t; b->remain -= t; if (b->remain == 0) b->st = 2;
        } else {
            if (p[i++] == '\n') b->st = 0;
        }
    }
    return 0;
}

static int sink_audio(const unsigned char *p, int n, void *u);

/* возвращает HTTP-статус или -1 */
static int http_do(const char *host, const char *method, const char *path, const char *body,
                   SinkFn sink, void *ctx, int auth)
{
    Conn *c = conn_open(host); char req[2048]; unsigned char buf[2048]; char lo[2049];
    int have = 0, hend = -1, n, i, status = -1, r; Body bs; int bl = body ? (int)strlen(body) : 0;
    if (!c) return -1;
    n = _snprintf(req, sizeof req - 1, "%s %s HTTP/1.1\r\nHost: %s\r\n", method, path, host);
    if (auth == 1 || auth == 2) n += _snprintf(req + n, sizeof req - n - 1,
        "Authorization: OAuth %s\r\nX-Yandex-Music-Client: %s\r\n", C_token,
        auth == 2 ? C_dclient : "YandexMusicAndroid/24023621");
    if (auth == 3) n += _snprintf(req + n, sizeof req - n - 1, "User-Agent: YMP/1.1 (WM6 player)\r\n");
    if (body) n += _snprintf(req + n, sizeof req - n - 1,
        "Content-Type: %s\r\nContent-Length: %d\r\n",
        body[0] == '{' ? "application/json" : "application/x-www-form-urlencoded", bl);
    n += _snprintf(req + n, sizeof req - n - 1, "Accept-Encoding: identity\r\nConnection: close\r\n");
    if (sink == sink_audio && g_range > 0) n += _snprintf(req + n, sizeof req - n - 1, "Range: bytes=%ld-\r\n", (long)g_range);
    n += _snprintf(req + n, sizeof req - n - 1, "\r\n");
    if (auth && !strcmp(host, C_host)) dbg("Отправка запроса...");
    if (c_write(c, req, n) || (body && c_write(c, body, bl))) { if (auth && !strcmp(host, C_host)) dbg("Ошибка отправки"); goto out; }
    if (auth && !strcmp(host, C_host)) dbg("Ожидание ответа...");

    while (hend < 0 && have < (int)sizeof buf) {
        r = c_read(c, buf + have, (int)sizeof buf - have);
        if (r <= 0) { if (auth && !strcmp(host, C_host)) dbg("Нет ответа от сервера (код %d)", r); goto out; }
        have += r;
        for (i = 0; i + 3 < have; i++)
            if (buf[i] == '\r' && buf[i+1] == '\n' && buf[i+2] == '\r' && buf[i+3] == '\n') { hend = i; break; }
    }
    if (hend < 0) goto out;
    if (hend > 2047) hend = 2047;
    for (i = 0; i < hend; i++) lo[i] = (char)((buf[i] >= 'A' && buf[i] <= 'Z') ? buf[i] | 32 : buf[i]);
    lo[hend] = 0;
    status = atoi(lo + 9);
    g_resp_status = status;
    if (sink == sink_audio && status != 200 && status != 206) dbg("Аудио: HTTP %d", status);
    memset(&bs, 0, sizeof bs);
    if (strstr(lo, "transfer-encoding: chunked")) bs.mode = 2;
    else { char *cl = strstr(lo, "content-length:"); if (cl) { bs.mode = 1; bs.remain = atol(cl + 15); } }
    if (sink == sink_audio && g_range == 0) g_clen = (bs.mode == 1) ? bs.remain : 0;
    if (bs.mode == 1 && bs.remain == 0) goto out;

    r = feed(&bs, buf + hend + 4, have - hend - 4, sink, ctx);
    while (r == 0) {
        int k = c_read(c, buf, (int)sizeof buf); if (k <= 0) break;
        r = feed(&bs, buf, k, sink, ctx);
    }
out:
    conn_close(c); return status;
}

/* буфер под JSON-ответы API */
static char g_api[262144]; static int g_apilen;
static int sink_buf(const unsigned char *p, int n, void *u)
{
    (void)u;
    if (g_apilen + n >= (int)sizeof g_api - 1) n = (int)sizeof g_api - 1 - g_apilen;
    memcpy(g_api + g_apilen, p, n); g_apilen += n; g_api[g_apilen] = 0; return 0;
}
static int api_a(const char *method, const char *path, const char *body, int auth)
{
    g_apilen = 0; g_api[0] = 0;
    return http_do(C_host, method, path, body, sink_buf, 0, auth);
}
static int api(const char *method, const char *path, const char *body)
{
    return api_a(method, path, body, 1);
}

/* ----------------------------------------------------- мини-разбор JSON */
static const char *jfind(const char *s, const char *k)
{
    char pat[48]; const char *p = s; size_t L;
    if (!s) return 0;
    sprintf(pat, "\"%s\"", k); L = strlen(pat);
    while ((p = strstr(p, pat)) != 0) {
        p += L; while (*p == ' ') p++;
        if (*p == ':') { p++; while (*p == ' ') p++; return p; }
    }
    return 0;
}

static int jstr(const char *p, char *o, int cap)
{
    int n = 0;
    o[0] = 0;
    if (!p || *p != '"') return 0;
    p++;
    while (*p && *p != '"' && n < cap - 4) {
        if (*p == '\\') {
            p++;
            if (*p == 'u') {
                unsigned v = 0; int k;
                for (k = 1; k <= 4; k++) { char h = p[k]; v = v * 16 + (h <= '9' ? h - '0' : (h | 32) - 'a' + 10); }
                p += 4;
                if (v < 0x80) o[n++] = (char)v;
                else if (v < 0x800) { o[n++] = (char)(0xC0 | (v >> 6)); o[n++] = (char)(0x80 | (v & 63)); }
                else { o[n++] = (char)(0xE0 | (v >> 12)); o[n++] = (char)(0x80 | ((v >> 6) & 63)); o[n++] = (char)(0x80 | (v & 63)); }
            } else if (*p == 'n') o[n++] = ' ';
            else o[n++] = *p;
            p++;
        } else o[n++] = *p++;
    }
    o[n] = 0; return n;
}

/* как jstr, но \n остаётся переводом строки, поддержаны суррогатные пары (для текстов песен) */
static int jstr_full(const char *p, char *o, int cap)
{
    int n = 0;
    o[0] = 0;
    if (!p || *p != '"') return 0;
    p++;
    while (*p && *p != '"' && n < cap - 5) {
        if (*p == '\\') {
            p++;
            if (*p == 'u') {
                unsigned v = 0, lo2 = 0; int k;
                for (k = 1; k <= 4; k++) { char h = p[k]; v = v * 16 + (h <= '9' ? h - '0' : (h | 32) - 'a' + 10); }
                p += 5;
                if (v >= 0xD800 && v < 0xDC00 && p[0] == '\\' && p[1] == 'u') {
                    for (k = 2; k <= 5; k++) { char h = p[k]; lo2 = lo2 * 16 + (h <= '9' ? h - '0' : (h | 32) - 'a' + 10); }
                    p += 6; v = 0x10000 + ((v - 0xD800) << 10) + (lo2 - 0xDC00);
                }
                if (v < 0x80) o[n++] = (char)v;
                else if (v < 0x800) { o[n++] = (char)(0xC0 | (v >> 6)); o[n++] = (char)(0x80 | (v & 63)); }
                else if (v < 0x10000) { o[n++] = (char)(0xE0 | (v >> 12)); o[n++] = (char)(0x80 | ((v >> 6) & 63)); o[n++] = (char)(0x80 | (v & 63)); }
                else { o[n++] = (char)(0xF0 | (v >> 18)); o[n++] = (char)(0x80 | ((v >> 12) & 63)); o[n++] = (char)(0x80 | ((v >> 6) & 63)); o[n++] = (char)(0x80 | (v & 63)); }
                continue;
            } else if (*p == 'n') o[n++] = '\n';
            else if (*p == 'r') { /* пропускаем */ }
            else if (*p == 't') o[n++] = ' ';
            else o[n++] = *p;
            if (*p) p++;
        } else o[n++] = *p++;
    }
    o[n] = 0; return n;
}

static int jget(const char *obj, const char *k, char *o, int cap) { return jstr(jfind(obj, k), o, cap); }

static const char *skip_obj(const char *p)
{
    int d = 0;
    for (; *p; p++) {
        if (*p == '"') { for (p++; *p && *p != '"'; p++) if (*p == '\\' && p[1]) p++; }
        else if (*p == '{') d++;
        else if (*p == '}') { if (--d == 0) return p + 1; }
    }
    return p;
}

/* UTF-8 -> UTF-16 с обрезкой под размер буфера */
static void u2w(const char *src, WCHAR *dst, int cap)
{
    int n = (int)strlen(src), r = 0;
    while (n > 0 && !(r = MultiByteToWideChar(CP_UTF8, 0, src, n, dst, cap - 1))) n--;
    dst[r] = 0;
}

static void fmt_time(long s, char *o) { sprintf(o, "%ld:%02ld", s / 60, s % 60); }

/* ---------------------------------------------------------- список треков */
static void load_list(void)
{
    char uid[32], path[128], body[1024], t[200], ar[120], line[360], id[24];
    char likes[MAXL][24]; int nl = 0, i, b; const char *p; WCHAR w[360]; int st;

    status("Подключение...");
    st = api("GET", "/account/status", 0);
    if (st != 200) { if (st != -1) status("account/status: HTTP %d (токен? время?)", st); return; }
    p = jfind(g_api, "uid");
    if (!p) { status("uid не найден в ответе"); return; }
    for (i = 0; i < 30 && p[i] >= '0' && p[i] <= '9'; i++) uid[i] = p[i];
    uid[i] = 0;
    strcpy(g_uid, uid);
    jget(g_api, "login", g_login, sizeof g_login);
    if (!jget(g_api, "fullName", g_name, sizeof g_name)) jget(g_api, "displayName", g_name, sizeof g_name);
    p = jfind(g_api, "hasPlus"); g_plus = (p && !strncmp(p, "true", 4)) ? 1 : 0;
    u2w(g_name, g_wName, 64); u2w(g_login, g_wLogin, 48);

    sprintf(path, "/users/%s/likes/tracks", uid);
    status("Загрузка списка...");
    st = api("GET", path, 0);
    if (st != 200) { if (st != -1) status("likes/tracks: HTTP %d", st); return; }
    p = jfind(g_api, "tracks");
    while (p && nl < C_count && (p = jfind(p, "id")) != 0) {
        char *colon;
        jstr(p, id, sizeof id); p++;
        colon = strchr(id, ':'); if (colon) *colon = 0;
        strcpy(likes[nl++], id);
    }

    for (b = 0; b < nl; b += 20) {
        const char *a; int n = 0;
        strcpy(body, "track-ids=");
        for (i = b; i < nl && i < b + 20; i++) { if (i > b) strcat(body, ","); strcat(body, likes[i]); }
        st = api("POST", "/tracks", body);
        if (st != 200) { if (st != -1) status("tracks: HTTP %d", st); return; }
        a = jfind(g_api, "result"); if (a && *a == '[') a++;
        while (a && *a && g_nt < MAXT) {
            const char *e; char sv, *eptr; const char *arr;
            while (*a && *a != '{' && *a != ']') a++;
            if (*a != '{') break;
            e = skip_obj(a); eptr = (char *)e; sv = *eptr; *eptr = 0;
            jget(a, "id", g_ids[g_nt], 24);
            jget(a, "title", t, sizeof t);
            ar[0] = 0; arr = jfind(a, "artists"); if (arr) jget(arr, "name", ar, sizeof ar);
            jget(a, "coverUri", g_cover[g_nt], 128);
            { const char *lp = jfind(a, "lyricsAvailable"); g_lyr[g_nt] = (lp && !strncmp(lp, "true", 4)) ? 1 : 0; }
            *eptr = sv;
            _snprintf(line, sizeof line - 1, "%s - %s", ar, t); line[sizeof line - 1] = 0;
            MultiByteToWideChar(CP_UTF8, 0, line, -1, w, 360);
            SendMessageW(g_list, LB_ADDSTRING, 0, (LPARAM)w);
            u2w(t, g_ttl[g_nt], 96); u2w(ar, g_art[g_nt], 64);
            g_liked[g_nt] = 1;
            g_nt++; n++; a = e;
        }
    }
    g_nlikes = g_nt;
    status("Треков: %d. Тап/Enter - играть", g_nt);
}

/* -------------------------------------------------------------- плеер */
#define RING_SZ (192 * 1024)
#define NB 8
static unsigned char g_ring[RING_SZ];
static volatile DWORD g_rd, g_wr;
static volatile int g_dl_done, g_stopdl;
static volatile int g_pending = -1;           /* -1 нет, -2 стоп, >=0 индекс трека */
static volatile int g_cur = -1, g_paused;
static HANDLE g_ev;
static HWAVEOUT g_hwo;
static WAVEHDR g_hdr[NB]; static short g_wbuf[NB][1152 * 2];

typedef struct {
    char host[96], path[1024];
    mbedtls_aes_context aes; int haskey; size_t off;
    unsigned char nonce[16], sb[16];
    int checked; long start_off;
} DL;

static int ring_put(const unsigned char *p, int n)
{
    while (n > 0) {
        DWORD avail, pos, c;
        if (g_pending != -1 || g_stopdl) return 1;
        avail = RING_SZ - (g_wr - g_rd);
        if (avail == 0) { Sleep(10); continue; }
        pos = g_wr % RING_SZ; c = (DWORD)n; if (c > avail) c = avail; if (c > RING_SZ - pos) c = RING_SZ - pos;
        memcpy(g_ring + pos, p, c); g_wr += c; p += c; n -= (int)c;
    }
    return 0;
}

static int sink_audio(const unsigned char *p, int n, void *u)
{
    DL *d = (DL *)u; unsigned char tmp[1024];
    if (!d->checked) {
        d->checked = 1;
        if (d->start_off > 0 && g_resp_status == 200) {   /* сервер проигнорировал Range и шлёт файл с начала */
            memset(d->nonce, 0, 16); d->off = 0; memset(d->sb, 0, 16); g_seek_ignored = 1;
        }
    }
    if (!d->haskey) return ring_put(p, n);
    while (n > 0) {
        int k = n > (int)sizeof tmp ? (int)sizeof tmp : n;
        mbedtls_aes_crypt_ctr(&d->aes, k, &d->off, d->nonce, d->sb, p, tmp);
        if (ring_put(tmp, k)) return 1;
        p += k; n -= k;
    }
    return 0;
}

static DL g_dl;
static DWORD WINAPI dl_thread(LPVOID x)
{
    (void)x;
    http_do(g_dl.host, "GET", g_dl.path, 0, sink_audio, &g_dl, 0);
    g_dl_done = 1; return 0;
}

static void make_sign2(const char *key, const char *msg, char *out, int strip)
{
    unsigned char d[32]; char b[64]; size_t ol = 0, i; char *o = out;
    mbedtls_md_hmac(mbedtls_md_info_from_type(MBEDTLS_MD_SHA256), (const unsigned char *)key, strlen(key),
                    (const unsigned char *)msg, strlen(msg), d);
    mbedtls_base64_encode((unsigned char *)b, sizeof b, &ol, d, 32);
    for (i = 0; i < ol; i++) {
        if (b[i] == '=') { if (strip) break; strcpy(o, "%3D"); o += 3; }
        else if (b[i] == '+') { strcpy(o, "%2B"); o += 3; }
        else if (b[i] == '/') { strcpy(o, "%2F"); o += 3; }
        else *o++ = b[i];
    }
    *o = 0;
}

static void make_sign(const char *msg, char *out) { make_sign2(C_hmac, msg, out, 1); }

static void wave_open(int hz, int ch)
{
    WAVEFORMATEX wf; int k;
    memset(&wf, 0, sizeof wf);
    wf.wFormatTag = WAVE_FORMAT_PCM; wf.nChannels = (WORD)ch; wf.nSamplesPerSec = hz;
    wf.wBitsPerSample = 16; wf.nBlockAlign = (WORD)(ch * 2); wf.nAvgBytesPerSec = hz * ch * 2;
    if (waveOutOpen(&g_hwo, WAVE_MAPPER, &wf, 0, 0, CALLBACK_NULL) != MMSYSERR_NOERROR) { g_hwo = 0; return; }
    for (k = 0; k < NB; k++) {
        memset(&g_hdr[k], 0, sizeof(WAVEHDR));
        g_hdr[k].lpData = (LPSTR)g_wbuf[k]; g_hdr[k].dwBufferLength = sizeof g_wbuf[k];
        waveOutPrepareHeader(g_hwo, &g_hdr[k], sizeof(WAVEHDR));
        g_hdr[k].dwFlags |= WHDR_DONE;
    }
}

static int wave_write(const short *pcm, int bytes)
{
    int k;
    for (;;) {
        if (g_pending != -1) return 1;
        for (k = 0; k < NB; k++)
            if (g_hdr[k].dwFlags & WHDR_DONE) {
                memcpy(g_wbuf[k], pcm, bytes);
                g_hdr[k].dwBufferLength = bytes;
                waveOutWrite(g_hwo, &g_hdr[k], sizeof(WAVEHDR));
                return 0;
            }
        Sleep(10);
    }
}

static void wave_close(int drain)
{
    int k;
    if (!g_hwo) return;
    if (g_paused) { waveOutRestart(g_hwo); g_paused = 0; }
    if (drain) for (;;) {
        int busy = 0;
        for (k = 0; k < NB; k++) if (!(g_hdr[k].dwFlags & WHDR_DONE)) busy = 1;
        if (!busy || g_pending != -1) break;
        Sleep(20);
    }
    waveOutReset(g_hwo);
    for (k = 0; k < NB; k++) waveOutUnprepareHeader(g_hwo, &g_hdr[k], sizeof(WAVEHDR));
    waveOutClose(g_hwo); g_hwo = 0;
}

/* окошко с ошибкой + начало ответа сервера (чтобы текст не закрывала клавиатура) */
static void err_box(const char *what, int st)
{
    char m[420]; WCHAR wm[420];
    _snprintf(m, sizeof m - 1, "%s (HTTP %d)\n%.260s", what, st, g_api);
    m[sizeof m - 1] = 0;
    u2w(m, wm, 420);
    MessageBoxW(g_hwnd, wm, L"YMP", MB_OK);
}

static void msg_box(const char *what, int st, const char *body)
{
    char m[420]; WCHAR wm[420];
    _snprintf(m, sizeof m - 1, "%s (HTTP %d)\n%.260s", what, st, body ? body : "");
    m[sizeof m - 1] = 0;
    u2w(m, wm, 420);
    MessageBoxW(g_hwnd, wm, L"YMP", MB_OK);
}

/* секунды с 1970 по UTC (не зависит от time() в cegcc) */
static unsigned long utc_epoch(void)
{
    SYSTEMTIME st; FILETIME ft; ULARGE_INTEGER u;
    GetSystemTime(&st); SystemTimeToFileTime(&st, &ft);
    u.LowPart = ft.dwLowDateTime; u.HighPart = ft.dwHighDateTime;
    return (unsigned long)((u.QuadPart - 116444736000000000ULL) / 10000000ULL);
}

static int play_track(int idx)
{
    char ts[16], msg[160], sig[96], path[400], url[1024], key[80];
    static const char *const tr[2] = { "raw", "encraw" };
    int st, rc = 0, have = 0, nfr = 0, k; const char *q, *s; HANDLE ht;
    static mp3dec_t dec; static unsigned char inb[16384]; static short pcm[MINIMP3_MAX_SAMPLES_PER_FRAME];

    status("Запрос ссылки...");
    for (k = 0; k < 2; k++) {   /* сначала raw (без шифрования), потом encraw */
        sprintf(ts, "%lu", utc_epoch());
        sprintf(msg, "%s%s%smp3%s", ts, g_ids[idx], C_quality, tr[k]);
        make_sign(msg, sig);
        sprintf(path, "/get-file-info?ts=%s&trackId=%s&quality=%s&codecs=mp3&transports=%s&sign=%s",
                ts, g_ids[idx], C_quality, tr[k], sig);
        st = api_a("GET", path, 0, 2);   /* 2 = заголовок десктопного клиента */
        if (st == 200 || st == -1) break;
    }
    if (st != 200) {
        if (st != -1) { status("get-file-info: HTTP %d", st); err_box("get-file-info", st); }
        return 2;
    }
    if (!jget(g_api, "url", url, sizeof url)) { status("В ответе нет url"); err_box("Нет url в ответе", st); return 2; }
    key[0] = 0; jget(g_api, "key", key, sizeof key);

    memset(&g_dl, 0, sizeof g_dl);
    s = strstr(url, "://"); s = s ? s + 3 : url;
    q = strchr(s, '/'); if (!q) return 2;
    memcpy(g_dl.host, s, q - s < 95 ? q - s : 95);
    strncpy(g_dl.path, q, sizeof g_dl.path - 1);
    mbedtls_aes_init(&g_dl.aes);
    if (key[0]) {
        unsigned char kb[32]; int i, kl = (int)strlen(key) / 2;
        if (kl != 16 && kl != 32) { status("Странный ключ (%d)", kl); return 2; }
        for (i = 0; i < kl; i++) { unsigned v; sscanf(key + 2 * i, "%2x", &v); kb[i] = (unsigned char)v; }
        mbedtls_aes_setkey_enc(&g_dl.aes, kb, kl * 8);
        g_dl.haskey = 1;   /* nonce = 16 нулей, счётчик с 0 */
    }

    g_rd = g_wr = 0; g_dl_done = 0; g_stopdl = 0; g_paused = 0;
    g_elapsed_ms = 0; g_total_s = 0; g_clen = 0; g_range = 0; g_seek_pm = -1; g_seek_ignored = 0;
    ht = CreateThread(NULL, 0, dl_thread, NULL, 0, NULL);
    mp3dec_init(&dec);
    status("Играет #%d", idx + 1);

    for (;;) {
        mp3dec_frame_info_t fi; int s2;
        if (g_pending != -1) { rc = 1; break; }
        if (g_seek_ignored) { g_seek_ignored = 0; g_elapsed_ms = 0; status("Сервер не поддерживает перемотку"); }
        if (g_seek_pm >= 0) {                       /* перемотка: заново качаем файл с нужного байта */
            int pm2 = g_seek_pm; long off;
            g_seek_pm = -1;
            if (g_total_s > 0 && g_clen > 0 && g_hwo) {
                off = (long)((long long)g_clen * pm2 / 1000);
                if (off > g_clen - 8192) off = g_clen - 8192;
                if (off < 0) off = 0;
                off &= ~15L;                         /* кратно 16 - нужно для расшифровки AES-CTR */
                g_stopdl = 1; WaitForSingleObject(ht, INFINITE); CloseHandle(ht);
                waveOutReset(g_hwo); g_paused = 0;
                g_rd = g_wr = 0; have = 0; g_dl_done = 0; g_stopdl = 0;
                g_range = off;
                memset(g_dl.nonce, 0, 16);
                { long blk = off / 16;
                  g_dl.nonce[12] = (unsigned char)(blk >> 24); g_dl.nonce[13] = (unsigned char)(blk >> 16);
                  g_dl.nonce[14] = (unsigned char)(blk >> 8);  g_dl.nonce[15] = (unsigned char)blk; }
                g_dl.off = 0; memset(g_dl.sb, 0, 16); g_dl.checked = 0; g_dl.start_off = off;
                ht = CreateThread(NULL, 0, dl_thread, NULL, 0, NULL);
                g_elapsed_ms = (long)pm2 * g_total_s;
                mp3dec_init(&dec);
            }
        }
        while (have < (int)sizeof inb && g_rd != g_wr) {
            DWORD pos = g_rd % RING_SZ, c = g_wr - g_rd;
            if (c > (DWORD)(sizeof inb - have)) c = sizeof inb - have;
            if (c > RING_SZ - pos) c = RING_SZ - pos;
            memcpy(inb + have, g_ring + pos, c); g_rd += c; have += (int)c;
        }
        if (have < 4096 && !g_dl_done) { Sleep(20); continue; }
        if (have == 0 && g_dl_done && g_rd == g_wr) break;
        s2 = mp3dec_decode_frame(&dec, inb, have, pcm, &fi);
        if (fi.frame_bytes == 0) {
            if (g_dl_done && g_rd == g_wr) break;
            if (have >= (int)sizeof inb) have = 0; else Sleep(10);
            continue;
        }
        memmove(inb, inb + fi.frame_bytes, have - fi.frame_bytes); have -= fi.frame_bytes;
        if (s2 > 0) {
            if (!g_hwo) { wave_open(fi.hz, fi.channels); if (!g_hwo) { status("waveOut не открылся"); rc = 2; break; } }
            if (wave_write(pcm, s2 * fi.channels * 2)) { rc = 1; break; }
            g_elapsed_ms += (long)((long long)s2 * 1000 / fi.hz);
            if (fi.bitrate_kbps > 0 && g_clen > 0) g_total_s = g_clen / (fi.bitrate_kbps * 125);
            if ((++nfr & 7) == 0) PostMessageW(g_hwnd, WM_APP + 3, 0, 0);
        }
    }
    g_stopdl = 1;
    wave_close(rc == 0);
    WaitForSingleObject(ht, INFINITE); CloseHandle(ht);
    mbedtls_aes_free(&g_dl.aes);
    return rc;
}

/* ---- обложка трека: скачиваем JPEG, декодируем, отдаём окну ---- */
typedef struct { unsigned char *rgb; int w, h; } CoverImg;
typedef struct { unsigned char *buf; int len, cap; } CBuf;

static int sink_cover(const unsigned char *p, int n, void *u)
{
    CBuf *c = (CBuf *)u;
    if (c->len + n > c->cap) return 1;
    memcpy(c->buf + c->len, p, n); c->len += n; return 0;
}

static DWORD WINAPI cover_thread(LPVOID x)
{
    int idx = (int)(size_t)x, st, w = 0, h = 0, comp = 0; char host[128], path[256], tmp[256], *sl, *pc;
    CBuf cb; unsigned char *rgb; CoverImg *ci;
    if (idx < 0 || idx >= g_nt || !g_cover[idx][0]) return 0;
    strncpy(host, g_cover[idx], sizeof host - 1); host[sizeof host - 1] = 0;
    sl = strchr(host, '/'); if (!sl) return 0;
    strncpy(path, sl, sizeof path - 1); path[sizeof path - 1] = 0;
    *sl = 0;
    pc = strstr(path, "%%"); if (!pc) return 0;
    *pc = 0;
    _snprintf(tmp, sizeof tmp - 1, "%s200x200%s", path, pc + 2); tmp[sizeof tmp - 1] = 0;
    cb.cap = 150 * 1024; cb.len = 0; cb.buf = (unsigned char *)malloc(cb.cap);
    if (!cb.buf) return 0;
    st = http_do(host, "GET", tmp, 0, sink_cover, &cb, 0);
    if (st == 200 && cb.len > 0) {
        rgb = stbi_load_from_memory(cb.buf, cb.len, &w, &h, &comp, 3);
        if (rgb) {
            ci = (CoverImg *)malloc(sizeof *ci);
            if (ci) {
                ci->rgb = rgb; ci->w = w; ci->h = h;
                if (!PostMessageW(g_hwnd, WM_APP + 4, idx, (LPARAM)ci)) { stbi_image_free(rgb); free(ci); }
            } else stbi_image_free(rgb);
        }
    }
    free(cb.buf);
    return 0;
}

static int sink_null(const unsigned char *p, int n, void *u) { (void)p; (void)n; (void)u; return 0; }

/* ---- история прослушанного: чтобы волна не повторяла треки (и в этой сессии, и между запусками) ---- */
#define HISTN 300
static char g_hist[HISTN][24];
static int g_nh, g_hh;                 /* g_nh = сколько записано, g_hh = куда писать следующий */
static CRITICAL_SECTION g_hcs;

static void hist_path(WCHAR *p)
{
    WCHAR *dot;
    GetModuleFileNameW(NULL, p, MAX_PATH);
    dot = wcsrchr(p, L'.'); if (dot) wcscpy(dot, L".hist");
}

static int hist_has(const char *id)
{
    int i, r = 0;
    EnterCriticalSection(&g_hcs);
    for (i = 0; i < g_nh; i++) if (!strcmp(g_hist[i], id)) { r = 1; break; }
    LeaveCriticalSection(&g_hcs);
    return r;
}

static void hist_push(const char *id)
{
    strncpy(g_hist[g_hh], id, 23); g_hist[g_hh][23] = 0;
    g_hh = (g_hh + 1) % HISTN; if (g_nh < HISTN) g_nh++;
}

static void hist_load(void)
{
    WCHAR p[MAX_PATH]; static char buf[HISTN * 24 + 64]; DWORD n = 0; HANDLE h; char *line, *nx;
    hist_path(p);
    h = CreateFileW(p, GENERIC_READ, FILE_SHARE_READ, NULL, OPEN_EXISTING, 0, NULL);
    if (h == INVALID_HANDLE_VALUE) return;
    {   /* читаем только хвост файла - последние записи */
        DWORD sz = GetFileSize(h, NULL), cap = sizeof buf - 1;
        if (sz != 0xFFFFFFFF && sz > cap) SetFilePointer(h, (LONG)(sz - cap), NULL, FILE_BEGIN);
    }
    ReadFile(h, buf, sizeof buf - 1, &n, NULL); CloseHandle(h); buf[n] = 0;
    EnterCriticalSection(&g_hcs);
    for (line = buf; line && *line; line = nx) {
        char *e;
        nx = strchr(line, '\n'); if (nx) *nx++ = 0;
        e = line + strlen(line); while (e > line && (e[-1] == '\r' || e[-1] == ' ')) *--e = 0;
        if (*line >= '0' && *line <= '9' && strlen(line) < 23) hist_push(line);
    }
    LeaveCriticalSection(&g_hcs);
}

static void hist_add(const char *id)
{
    WCHAR p[MAX_PATH]; HANDLE h; DWORD n; char a[40];
    if (!id[0] || hist_has(id)) return;
    EnterCriticalSection(&g_hcs); hist_push(id); LeaveCriticalSection(&g_hcs);
    hist_path(p);
    h = CreateFileW(p, GENERIC_WRITE, FILE_SHARE_READ, NULL, OPEN_ALWAYS, 0, NULL);
    if (h != INVALID_HANDLE_VALUE) {
        if (GetFileSize(h, NULL) > 20000) SetEndOfFile(h);      /* файл не растёт бесконечно */
        SetFilePointer(h, 0, NULL, FILE_END);
        _snprintf(a, sizeof a - 1, "%s\r\n", id); a[sizeof a - 1] = 0;
        WriteFile(h, a, (DWORD)strlen(a), &n, NULL); CloseHandle(h);
    }
}

/* ---- обратная связь "Моей волне": что включили / доиграли / пропустили. Без неё сервер не знает, что уже слышали ---- */
typedef struct { char type[16], id[24], rsid[96], batch[96]; long secs; } FB;
static volatile int g_fb_off, g_fb_fail;

static DWORD WINAPI feedback_thread(LPVOID x)
{
    FB *f = (FB *)x; char path[160], body[480]; int st;
    SetThreadPriority(GetCurrentThread(), THREAD_PRIORITY_BELOW_NORMAL);
    sprintf(path, "/rotor/session/%s/feedback", f->rsid);
    if (f->id[0])
        _snprintf(body, sizeof body - 1, "{\"event\":{\"type\":\"%s\",\"timestamp\":%lu,\"trackId\":\"%s\",\"totalPlayedSeconds\":%ld},\"batchId\":\"%s\"}",
                  f->type, utc_epoch(), f->id, f->secs, f->batch);
    else
        _snprintf(body, sizeof body - 1, "{\"event\":{\"type\":\"%s\",\"timestamp\":%lu},\"batchId\":\"%s\"}", f->type, utc_epoch(), f->batch);
    body[sizeof body - 1] = 0;
    st = http_do(C_host, "POST", path, body, sink_null, 0, 1);
    logline("feedback %s %s -> HTTP %d", f->type, f->id, st);
    if (st == 200) g_fb_fail = 0;
    else if (st >= 400 && ++g_fb_fail >= 3) { g_fb_off = 1; logline("feedback отключён (3 ошибки подряд)"); }
    free(f);
    return 0;
}

static void rotor_feedback(const char *type, const char *id, long secs)
{
    FB *f; HANDLE t;
    if (g_fb_off || !g_rsid[0]) return;
    f = (FB *)calloc(1, sizeof *f); if (!f) return;
    strncpy(f->type, type, 15); strncpy(f->id, id ? id : "", 23);
    strncpy(f->rsid, g_rsid, 95); strncpy(f->batch, g_batch, 95); f->secs = secs;
    t = CreateThread(NULL, 0, feedback_thread, f, 0, NULL);
    if (t) CloseHandle(t); else free(f);
}

/* ---- очередь: сохранить/вернуть список любимых, пока играет волна ---- */
static struct {
    char ids[MAXT][24]; WCHAR ttl[MAXT][96], art[MAXT][64]; char cover[MAXT][128]; int liked[MAXT]; int lyr[MAXT]; int nt;
} g_sv;

static void queue_save(void)
{
    int i;
    memcpy(g_sv.ids, g_ids, sizeof g_ids); memcpy(g_sv.ttl, g_ttl, sizeof g_ttl);
    memcpy(g_sv.art, g_art, sizeof g_art); memcpy(g_sv.cover, g_cover, sizeof g_cover);
    for (i = 0; i < MAXT; i++) { g_sv.liked[i] = g_liked[i]; g_sv.lyr[i] = g_lyr[i]; }
    g_sv.nt = g_nt; g_saved = 1;
}

static void queue_restore(void)
{
    int i;
    if (!g_saved) return;
    memcpy(g_ids, g_sv.ids, sizeof g_ids); memcpy(g_ttl, g_sv.ttl, sizeof g_ttl);
    memcpy(g_art, g_sv.art, sizeof g_art); memcpy(g_cover, g_sv.cover, sizeof g_cover);
    for (i = 0; i < MAXT; i++) { g_liked[i] = g_sv.liked[i]; g_lyr[i] = g_sv.lyr[i]; }
    g_nt = g_sv.nt;
}

static volatile int g_listkind = 1;   /* что сейчас в списке: 1 = текущая очередь (волна/поиск/любимые), 0 = экран "Любимое" */

static void list_add_line(int i)
{
    WCHAR w[200];
    if (g_listkind != 1) return;           /* на экране "Любимое" очередь в список не дописываем */
    wcsncpy(w, g_art[i], 63); w[63] = 0; wcscat(w, L" - "); wcsncat(w, g_ttl[i], 95);
    SendMessageW(g_list, LB_ADDSTRING, 0, (LPARAM)w);
}

/* список = текущая очередь */
static void list_rebuild(void)
{
    int i;
    g_listkind = 1;
    SendMessageW(g_list, LB_RESETCONTENT, 0, 0);
    for (i = 0; i < g_nt; i++) list_add_line(i);
    if (g_cur >= 0 && g_cur < g_nt) SendMessageW(g_list, LB_SETCURSEL, g_cur, 0);
}

/* число любимых и их названия: если играет волна/поиск, любимые лежат в сохранённой копии очереди */
static int likes_count(void) { return g_mode == 0 ? g_nt : (g_saved ? g_sv.nt : 0); }

/* список = любимые (очередь и воспроизведение не трогаем) */
static void likes_fill(void)
{
    int i, n = likes_count(); WCHAR w[200];
    g_listkind = 0;
    SendMessageW(g_list, LB_RESETCONTENT, 0, 0);
    for (i = 0; i < n; i++) {
        const WCHAR *ar = g_mode == 0 ? g_art[i] : g_sv.art[i], *tt = g_mode == 0 ? g_ttl[i] : g_sv.ttl[i];
        wcsncpy(w, ar, 63); w[63] = 0; wcscat(w, L" - "); wcsncat(w, tt, 95);
        SendMessageW(g_list, LB_ADDSTRING, 0, (LPARAM)w);
    }
}

/* уже есть в очереди? */
static int in_queue(const char *id)
{
    int i;
    for (i = 0; i < g_nt; i++) if (!strcmp(g_ids[i], id)) return 1;
    return 0;
}

/* разобрать массив sequence из ответа "Моей волны" и дописать новые треки в очередь; возвращает сколько добавлено.
   strict=1: пропускать и те, что уже играли раньше (история); дубли внутри очереди пропускаются всегда */
static int wave_add_items(const char *json, int strict)
{
    const char *a = jfind(json, "sequence"); int n = 0;
    if (!a || *a != '[') return 0;
    a++;
    while (*a && g_nt < MAXT) {
        const char *e, *tp;
        while (*a && *a != '{' && *a != ']') a++;
        if (*a != '{') break;
        e = skip_obj(a);
        tp = jfind(a, "track");
        if (tp && tp < e && *tp == '{') {
            const char *te = skip_obj(tp), *arr; char sv, *ep, t[200], ar[120], *colon;
            ep = (char *)te; sv = *ep; *ep = 0;
            g_ids[g_nt][0] = 0; g_cover[g_nt][0] = 0; t[0] = 0; ar[0] = 0;
            jget(tp, "id", g_ids[g_nt], 24);
            colon = strchr(g_ids[g_nt], ':'); if (colon) *colon = 0;
            jget(tp, "title", t, sizeof t);
            arr = jfind(tp, "artists"); if (arr) jget(arr, "name", ar, sizeof ar);
            jget(tp, "coverUri", g_cover[g_nt], 128);
            { const char *lp = jfind(tp, "lyricsAvailable"); g_lyr[g_nt] = (lp && !strncmp(lp, "true", 4)) ? 1 : 0; }
            *ep = sv;
            if (g_ids[g_nt][0] && !in_queue(g_ids[g_nt]) && !(strict && hist_has(g_ids[g_nt]))) {
                u2w(t, g_ttl[g_nt], 96); u2w(ar, g_art[g_nt], 64);
                g_liked[g_nt] = 0;
                g_nt++; n++;
            }
        }
        a = e;
    }
    return n;
}

static void play_idx(int i);

/* дозагрузка следующей партии волны (в фоне, со своим буфером).
   queue = id последнего трека очереди (как в официальном клиенте). Если пришли одни повторы - просим ещё раз */
static DWORD WINAPI wave_more_thread(LPVOID x)
{
    char body[512], path[160]; int i, from, st = 0, n = 0, old, pass, form = 0; CBuf cb;
    (void)x;
    if (g_mode != 1 || !g_rsid[0] || g_nt >= MAXT) { g_morebusy = 0; return 0; }
    sprintf(path, "/rotor/session/%s/tracks", g_rsid);
    cb.cap = 200 * 1024; cb.len = 0; cb.buf = (unsigned char *)malloc(cb.cap + 1);
    if (!cb.buf) { g_morebusy = 0; return 0; }
    for (pass = 0; pass < 4 && n == 0 && g_mode == 1; pass++) {
        if (form == 0) {
            sprintf(body, "{\"queue\":\"%s\"}", g_nt > 0 ? g_ids[g_nt - 1] : "");
        } else {                                      /* запасной вариант: массив последних id */
            from = g_nt > 5 ? g_nt - 5 : 0;
            strcpy(body, "{\"queue\":[");
            for (i = from; i < g_nt; i++) {
                if (i > from) strcat(body, ",");
                strcat(body, "\""); strcat(body, g_ids[i]); strcat(body, "\"");
            }
            strcat(body, "]}");
        }
        cb.len = 0;
        st = http_do(C_host, "POST", path, body, sink_cover, &cb, 1);
        cb.buf[cb.len] = 0;
        logline("rotor/tracks form=%d pass=%d -> HTTP %d", form, pass, st);
        if (st == -1) break;
        if (st != 200) {
            if (form == 0) { form = 1; continue; }
            status("Волна (продолжение): HTTP %d", st); break;
        }
        jget((const char *)cb.buf, "batchId", g_batch, sizeof g_batch);
        old = g_nt;
        n = wave_add_items((const char *)cb.buf, pass < 2);   /* последний круг - допускаем уже игранное */
        for (i = old; i < old + n; i++) list_add_line(i);
    }
    if (st == 200 && n == 0) status("Волна: новых треков нет");
    free(cb.buf);
    g_morebusy = 0;
    return 0;
}

/* старт "Моей волны": новая сессия, очередь заменяется её треками */
static DWORD WINAPI wave_thread(LPVOID x)
{
    int st, n;
    (void)x;
    status("Моя волна: запуск...");
    st = api_a("POST", "/rotor/session/new",
               "{\"seeds\":[\"user:onyourwave\"],\"includeTracksInResponse\":true}", 1);
    if (st != 200) { if (st != -1) { status("Моя волна: HTTP %d", st); err_box("Моя волна", st); } return 0; }
    g_rsid[0] = 0; g_batch[0] = 0;
    if (!jget(g_api, "radioSessionId", g_rsid, sizeof g_rsid)) { err_box("Нет radioSessionId", st); return 0; }
    jget(g_api, "batchId", g_batch, sizeof g_batch);

    g_pending = -2; SetEvent(g_ev);                 /* остановить то, что играло */
    if (g_mode == 0) queue_save();
    g_mode = 1; g_nt = 0; g_cur = -1; g_coverIdx = -1; g_morebusy = 0;
    n = wave_add_items(g_api, 1);
    if (n == 0) n = wave_add_items(g_api, 0);       /* всё уже слышали - берём как есть */
    if (n == 0) {
        queue_restore(); g_mode = 0; list_rebuild();
        err_box("Волна не прислала треков", st);
        return 0;
    }
    list_rebuild();
    status("Моя волна: %d треков", n);
    rotor_feedback("radioStarted", "", 0);
    play_idx(0);
    return 0;
}

/* профиль: имя, логин и аватар с login.yandex.ru (если токен это разрешает) */
static DWORD WINAPI profile_thread(LPVOID x)
{
    CBuf pb, ab; int st, w = 0, h = 0, comp = 0; char id[96], nm[64], path[200];
    unsigned char *rgb; CoverImg *ci;
    (void)x;
    pb.cap = 6000; pb.len = 0; pb.buf = (unsigned char *)malloc(pb.cap + 1);
    if (!pb.buf) return 0;
    st = http_do("login.yandex.ru", "GET", "/info?format=json", 0, sink_cover, &pb, 1);
    id[0] = 0;
    if (st == 200 && pb.len > 0) {
        pb.buf[pb.len] = 0;
        if (jget((const char *)pb.buf, "real_name", nm, sizeof nm) && nm[0]) strncpy(g_name, nm, sizeof g_name - 1);
        else if (!g_name[0] && jget((const char *)pb.buf, "display_name", nm, sizeof nm)) strncpy(g_name, nm, sizeof g_name - 1);
        if (!g_login[0]) jget((const char *)pb.buf, "login", g_login, sizeof g_login);
        jget((const char *)pb.buf, "default_avatar_id", id, sizeof id);
        u2w(g_name, g_wName, 64); u2w(g_login, g_wLogin, 48);
        PostMessageW(g_hwnd, WM_APP + 3, 1, 0);
    }
    free(pb.buf);
    if (id[0] && !strstr(id, "0/0-0")) {
        ab.cap = 150 * 1024; ab.len = 0; ab.buf = (unsigned char *)malloc(ab.cap);
        if (!ab.buf) return 0;
        _snprintf(path, sizeof path - 1, "/get-yapic/%s/islands-200", id); path[sizeof path - 1] = 0;
        st = http_do("avatars.mds.yandex.net", "GET", path, 0, sink_cover, &ab, 0);
        if (st == 200 && ab.len > 0) {
            rgb = stbi_load_from_memory(ab.buf, ab.len, &w, &h, &comp, 3);
            if (rgb) {
                ci = (CoverImg *)malloc(sizeof *ci);
                if (ci) {
                    ci->rgb = rgb; ci->w = w; ci->h = h;
                    if (!PostMessageW(g_hwnd, WM_APP + 6, 0, (LPARAM)ci)) { stbi_image_free(rgb); free(ci); }
                } else stbi_image_free(rgb);
            }
        }
        free(ab.buf);
    }
    return 0;
}

/* ---- поиск ---- */
static void url_encode(const char *s, char *o, int cap)
{
    static const char hexd[] = "0123456789ABCDEF"; int n = 0;
    for (; *s && n < cap - 4; s++) {
        unsigned char c = (unsigned char)*s;
        if ((c >= '0' && c <= '9') || (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || c == '-' || c == '_' || c == '.' || c == '~')
            o[n++] = (char)c;
        else { o[n++] = '%'; o[n++] = hexd[c >> 4]; o[n++] = hexd[c & 15]; }
    }
    o[n] = 0;
}

/* разобрать ответ поиска (tracks -> results[]) и дописать найденные треки в очередь */
static int search_add_items(const char *json, int store)
{
    const char *tr = jfind(json, "tracks"), *a; int n = 0;
    while (tr && *tr != '{') tr = jfind(tr + 1, "tracks");   /* нужен объект {"total":..,"results":[..]} */
    if (!tr) return 0;
    a = jfind(tr, "results");
    if (!a || *a != '[') return 0;
    a++;
    /* store=0 - просто считаем найденное: очередь при этом может быть любой длины (раньше тут стояло g_nt < MAXT,
       и при полной очереди волны поиск всегда отвечал "Ничего не найдено") */
    while (*a && (!store || g_nt < MAXT) && n < MAXT) {
        const char *e, *arr; char sv, *ep, t[200], ar[120], id[24], *colon;
        while (*a && *a != '{' && *a != ']') a++;
        if (*a != '{') break;
        e = skip_obj(a);
        ep = (char *)e; sv = *ep; *ep = 0;
        id[0] = 0; t[0] = 0; ar[0] = 0;
        jget(a, "id", id, sizeof id);
        colon = strchr(id, ':'); if (colon) *colon = 0;
        if (id[0]) {
            if (store) {
                strcpy(g_ids[g_nt], id); g_cover[g_nt][0] = 0;
                jget(a, "title", t, sizeof t);
                arr = jfind(a, "artists"); if (arr) jget(arr, "name", ar, sizeof ar);
                jget(a, "coverUri", g_cover[g_nt], 128);
                { const char *lp = jfind(a, "lyricsAvailable"); g_lyr[g_nt] = (lp && !strncmp(lp, "true", 4)) ? 1 : 0; }
                u2w(t, g_ttl[g_nt], 96); u2w(ar, g_art[g_nt], 64);
                g_liked[g_nt] = 0;
                g_nt++;
            }
            n++;
        }
        *ep = sv;
        a = e;
    }
    return n;
}

/* параметр x - строка запроса в UTF-8, выделенная через malloc (поток освобождает её) */
static DWORD WINAPI search_thread(LPVOID x)
{
    static const char *const types[2] = { "track", "all" };
    char *q = (char *)x, enc[400], path[480], note[96]; CBuf cb; int st = 0, n = 0, k;
    status("Поиск...");
    url_encode(q, enc, sizeof enc); free(q);
    cb.cap = 300 * 1024; cb.len = 0; cb.buf = (unsigned char *)malloc(cb.cap + 1);
    if (!cb.buf) return 0;
    for (k = 0; k < 2 && n == 0; k++) {        /* сначала только треки, потом "всё" */
        cb.len = 0;
        sprintf(path, "/search?text=%s&nocorrect=False&type=%s&page=0&playlist-in-best=True", enc, types[k]);
        st = http_do(C_host, "GET", path, 0, sink_cover, &cb, 1);
        cb.buf[cb.len] = 0;
        if (st != 200) break;
        n = search_add_items((const char *)cb.buf, 0);
    }
    if (st != 200) {
        msg_box("Поиск не удался", st, st == -1 ? "нет ответа от сервера" : (const char *)cb.buf);
        free(cb.buf); return 0;
    }
    if (n == 0) {
        logline("search '%s': 200, но треков нет. Ответ: %.200s", enc, cb.buf);
        if (jfind((const char *)cb.buf, "tracks")) msg_box("Ничего не найдено", st, "Попробуйте другой запрос");
        else msg_box("Поиск: неожиданный ответ", st, (const char *)cb.buf);
        free(cb.buf); return 0;
    }
    g_pending = -2; SetEvent(g_ev);                 /* новая очередь - прежняя музыка останавливается */
    if (g_mode == 0) queue_save();
    g_mode = 2; g_nt = 0; g_cur = -1; g_coverIdx = -1; g_morebusy = 0;
    n = search_add_items((const char *)cb.buf, 1);
    free(cb.buf);
    list_rebuild();
    PostMessageW(g_hwnd, WM_APP + 9, 0, 0);
    status("Найдено: %d. Двойной тап - играть", n);
    (void)note;
    return 0;
}

/* ---- текст песни: ссылка из /tracks/{id}/lyrics, затем сам текст по ссылке ---- */
#define LYR_KEY "p93jhgh689SBReK6ghtw62"   /* ключ подписи из Android-приложения (библиотека yandex-music) */

static void post_lyrics(const WCHAR *w)
{
    size_t n = wcslen(w); WCHAR *copy = (WCHAR *)malloc((n + 1) * sizeof(WCHAR));
    if (!copy) return;
    memcpy(copy, w, (n + 1) * sizeof(WCHAR));
    if (!PostMessageW(g_hwnd, WM_APP + 7, 0, (LPARAM)copy)) free(copy);
}

#define LYR_MAX 30000

/* UTF-8 текст -> окно: переводы строк \r\n, дальше post_lyrics */
static void show_lyrics_utf8(const char *u8)
{
    int len = (int)strlen(u8), n, i; WCHAR *w, *o;
    w = (WCHAR *)malloc((size_t)(len + 1) * sizeof(WCHAR) * 2);
    if (!w) return;
    n = MultiByteToWideChar(CP_UTF8, 0, u8, len, w + len + 1, len);
    o = w;
    for (i = 0; i < n; i++) {
        WCHAR c = w[len + 1 + i];
        if (c == L'\r') continue;
        if (c == L'\n') *o++ = L'\r';
        *o++ = c;
    }
    *o = 0;
    post_lyrics(w);
    free(w);
}

/* Текст песни. Три источника по очереди:
   1) /tracks/{id}/lyrics (подписанный запрос, затем ссылка downloadUrl) - основной способ Яндекса
   2) /tracks/{id}/supplement - старый способ, без подписи
   3) lrclib.net - открытая база текстов (не Яндекс), на случай если Яндекс отдаёт 403
   Результат каждого шага пишется в ymp.log, а при неудаче - ещё и в окно текста. */
static DWORD WINAPI lyrics_thread(LPVOID x)
{
    int idx = (int)(size_t)x, st, got = 0, k, n, st1 = 0, st2 = 0, st3 = 0;
    char id[24], msg[64], sig[100], path[1400], url[700], host[128], p2[600], *sl, *txt, *buf;
    char art8[200], ttl8[240], qs[800], qe[1200], diag[200]; CBuf cb; const char *lp;
    if (idx < 0 || idx >= g_nt) return 0;
    strcpy(id, g_ids[idx]);
    WideCharToMultiByte(CP_UTF8, 0, g_art[idx], -1, art8, sizeof art8 - 1, NULL, NULL); art8[sizeof art8 - 1] = 0;
    WideCharToMultiByte(CP_UTF8, 0, g_ttl[idx], -1, ttl8, sizeof ttl8 - 1, NULL, NULL); ttl8[sizeof ttl8 - 1] = 0;
    cb.cap = 128 * 1024; cb.len = 0; cb.buf = (unsigned char *)malloc(cb.cap + 1);
    txt = (char *)malloc(LYR_MAX + 8);
    if (!cb.buf || !txt) { free(cb.buf); free(txt); return 0; }
    buf = (char *)cb.buf; txt[0] = 0;
    status("Текст: запрос...");

    /* 1. подписанный запрос; при 403 пробуем второй вариант заголовка клиента (1 = Android, 2 = десктоп) */
    for (k = 1; k <= 2 && !got; k++) {
        unsigned long ts = utc_epoch();
        sprintf(msg, "%s%lu", id, ts);
        make_sign2(LYR_KEY, msg, sig, 0);
        sprintf(path, "/tracks/%s/lyrics?format=TEXT&timeStamp=%lu&sign=%s", id, ts, sig);
        cb.len = 0; st = http_do(C_host, "GET", path, 0, sink_cover, &cb, k); buf[cb.len] = 0;
        st1 = st;
        logline("lyrics[1] client=%d -> HTTP %d: %.150s", k, st, buf);
        if (st != 200) { if (st == 403) continue; break; }
        url[0] = 0; jget(buf, "downloadUrl", url, sizeof url);
        if (!url[0]) { logline("lyrics[1]: в ответе нет downloadUrl"); break; }
        sl = strstr(url, "://"); sl = sl ? sl + 3 : url;
        strncpy(host, sl, sizeof host - 1); host[sizeof host - 1] = 0;
        sl = strchr(host, '/'); if (!sl) break;
        strncpy(p2, sl, sizeof p2 - 1); p2[sizeof p2 - 1] = 0; *sl = 0;
        cb.len = 0; st = http_do(host, "GET", p2, 0, sink_cover, &cb, 3); buf[cb.len] = 0;
        logline("lyrics[1] файл %s -> HTTP %d, %d байт", host, st, cb.len);
        st1 = st;
        if (st == 200 && cb.len > 0) {
            n = cb.len < LYR_MAX ? cb.len : LYR_MAX;
            memcpy(txt, buf, n); txt[n] = 0; got = 1;
        }
    }

    /* 2. supplement */
    if (!got) {
        status("Текст: другой способ...");
        sprintf(path, "/tracks/%s/supplement", id);
        cb.len = 0; st = http_do(C_host, "GET", path, 0, sink_cover, &cb, 1); buf[cb.len] = 0;
        st2 = st;
        logline("lyrics[2] supplement -> HTTP %d: %.150s", st, buf);
        if (st == 200) {
            lp = jfind(buf, "lyrics");
            if (lp && *lp == '{') {
                const char *f = jfind(lp, "fullLyrics");
                if (!f || *f != '"') f = jfind(lp + 1, "lyrics");
                if (f && *f == '"' && jstr_full(f, txt, LYR_MAX) > 8) got = 1;
            }
        }
    }

    /* 3. lrclib.net */
    if (!got) {
        status("Текст: поиск в lrclib...");
        for (k = 0; k < 2 && !got; k++) {
            if (k == 0) _snprintf(qs, sizeof qs - 1, "%s %s", art8, ttl8); else _snprintf(qs, sizeof qs - 1, "%s", ttl8);
            qs[sizeof qs - 1] = 0;
            url_encode(qs, qe, sizeof qe);
            _snprintf(path, sizeof path - 1, "/api/search?q=%s", qe); path[sizeof path - 1] = 0;
            cb.len = 0; st = http_do("lrclib.net", "GET", path, 0, sink_cover, &cb, 3); buf[cb.len] = 0;
            st3 = st;
            logline("lyrics[3] lrclib q='%s' -> HTTP %d, %d байт", qs, st, cb.len);
            if (st != 200) break;
            lp = strchr(buf, '[');
            while (lp && *lp && !got) {                   /* первый элемент массива, где есть plainLyrics */
                const char *e, *pl; char sv, *ep;
                while (*lp && *lp != '{' && *lp != ']') lp++;
                if (*lp != '{') break;
                e = skip_obj(lp); ep = (char *)e; sv = *ep; *ep = 0;
                pl = jfind(lp, "plainLyrics");
                if (pl && *pl == '"' && jstr_full(pl, txt, LYR_MAX) > 8) got = 1;
                *ep = sv; lp = e;
            }
        }
    }

    if (got) {
        show_lyrics_utf8(txt);
        status("Текст песни загружен");
    } else {
        WCHAR none[200];
        _snprintf(diag, sizeof diag - 1, "Текст недоступен\n\nЯндекс: HTTP %d / %d\nlrclib: HTTP %d\n(подробности в ymp.log)", st1, st2, st3);
        diag[sizeof diag - 1] = 0;
        { char tmp[220]; int i, o = 0;           /* \n -> \r\n */
          for (i = 0; diag[i] && o < 210; i++) { if (diag[i] == '\n') tmp[o++] = '\r'; tmp[o++] = diag[i]; }
          tmp[o] = 0; u2w(tmp, none, 200); }
        post_lyrics(none);
        status("Текст: Яндекс %d/%d, lrclib %d", st1, st2, st3);
    }
    free(cb.buf); free(txt);
    return 0;
}

static DWORD WINAPI player_thread(LPVOID x)
{
    (void)x;
    for (;;) {
        WaitForSingleObject(g_ev, INFINITE);
        while (g_pending != -1) {
            int i = g_pending; int rc, wmode; char curid[24];
            g_pending = -1;
            if (i < 0) { g_active = 0; status("Стоп"); continue; }
            g_cur = i; g_active = 1;
            strcpy(curid, g_ids[i]); wmode = (g_mode == 1);
            hist_add(curid);
            if (wmode) rotor_feedback("trackStarted", curid, 0);
            if (g_mode == 1 && g_nt - i <= 3 && !g_morebusy) {
                HANDLE mh; g_morebusy = 1;
                mh = CreateThread(NULL, 0, wave_more_thread, NULL, 0, NULL);
                if (mh) CloseHandle(mh); else g_morebusy = 0;
            }
            PostMessageW(g_hwnd, WM_APP + 2, i, 0);
            if (i != g_coverIdx) { HANDLE ch = CreateThread(NULL, 0, cover_thread, (LPVOID)(size_t)i, 0, NULL); if (ch) CloseHandle(ch); }
            rc = play_track(i);
            if (wmode && g_mode == 1) {                 /* сообщаем волне, доиграли мы трек или пропустили */
                long secs = g_elapsed_ms / 1000;
                if (rc == 0) rotor_feedback("trackFinished", curid, secs);
                else if (rc == 1 && secs > 0) rotor_feedback("skip", curid, secs);
            }
            if (rc == 0 && g_pending == -1) {
                if (g_repeat) g_pending = i;
                else {
                    int wt;
                    for (wt = 0; wt < 80 && g_mode == 1 && g_morebusy && i + 1 >= g_nt && g_pending == -1; wt++) Sleep(100);
                    if (g_pending != -1) { /* пользователь уже выбрал другой трек */ }
                    else if (i + 1 < g_nt) g_pending = i + 1;
                    else { g_active = 0; status("Конец списка"); }
                }
            } else if (rc == 2 && g_pending == -1) g_active = 0;
        }
        PostMessageW(g_hwnd, WM_APP + 3, 1, 0);
    }
    return 0;
}

static void play_idx(int i)
{
    if (i < 0 || i >= g_nt) return;
    g_pending = i; SetEvent(g_ev);
}

static DWORD WINAPI loader_thread(LPVOID x)
{
    (void)x;
    if (!C_token[0] || !C_hmac[0]) { status("Заполните token и hmac в ymp.ini"); PostMessageW(g_hwnd, WM_APP + 8, 0, 0); return 0; }
    if (tls_init()) { status("Ошибка инициализации TLS"); PostMessageW(g_hwnd, WM_APP + 8, 0, 0); return 0; }
    load_list();
    { HANDLE ph = CreateThread(NULL, 0, profile_thread, NULL, 0, NULL); if (ph) CloseHandle(ph); }
    CreateThread(NULL, 0, player_thread, NULL, 0, NULL);
    if (C_autowave) wave_thread(NULL);              /* сразу включаем "Мою волну" */
    if (!(g_mode == 1 && g_nt > 0)) PostMessageW(g_hwnd, WM_APP + 8, 0, 0);   /* волна не запустилась: убрать анимацию */
    return 0;
}

/* ----------------------------------------------------------------- UI */
#define ID_LIST   100
#define ID_TOPLAY 101
#define ID_FIND   102
#define ID_EDIT   103
#define ID_LYR    104

#define K_BG    RGB(24, 24, 28)
#define K_BAR   RGB(36, 36, 42)
#define K_COVER RGB(48, 48, 56)
#define K_YEL   RGB(255, 204, 0)
#define K_WHITE RGB(240, 240, 240)
#define K_GRAY  RGB(130, 130, 138)
#define K_GRAY2 RGB(70, 70, 76)
#define K_RED   RGB(235, 60, 70)
#define K_DARK  RGB(40, 32, 0)

#define CXR(r) (((r).left + (r).right) / 2)
#define CYR(r) (((r).top + (r).bottom) / 2)

/* экраны: 0 = список, 1 = плеер, 2 = главное, 3 = профиль */
static HWND g_bplay;
static HBRUSH g_brBg;
static HFONT g_fTitle, g_fBig, g_fSmall;
static int g_view, g_W, g_H, g_sh, g_sy;
static RECT r_avatar, r_cover, r_tt, r_ar, r_prev, r_play, r_next, r_dis, r_like, r_prog, r_home, r_coll, r_bar;
static RECT r_wave, r_fav, r_prof, r_avbig, r_brep, r_bexit, r_progp;
static WCHAR g_wTitle[16], g_wHint[40], g_wHome[16], g_wWaveT[24], g_wWaveS[40], g_wFavT[24], g_wProfT[24], g_wProfile[16], g_wExit[16];
static HBITMAP g_hAvatar;
static HWND g_edit, g_bfind, g_lytext;
static RECT r_search, r_lyr;
static WCHAR g_wLyrLoad[32], g_wFind[16];
static volatile int g_drag, g_drag_pm;
static volatile int g_loading = 1, g_frame;   /* анимация загрузки в начале */

static const int HX[10] = { 0, -50, -95, -100, -60, 0, 60, 100, 95, 50 };
static const int HY[10] = { -35, -85, -55, -10, 40, 95, 40, -10, -55, -85 };


/* лайк (want=1) или снятие лайка (want=0), в отдельном потоке; параметр = (индекс << 1) | want */
static DWORD WINAPI like_thread(LPVOID x)
{
    int v = (int)(size_t)x, i = v >> 1, want = v & 1, st; char path[96], body[48];
    if (i < 0 || i >= g_nt || !g_uid[0]) return 0;
    sprintf(path, "/users/%s/likes/tracks/%s", g_uid, want ? "add-multiple" : "remove");
    sprintf(body, "track-ids=%s", g_ids[i]);
    st = http_do(C_host, "POST", path, body, sink_null, 0, 1);
    if (st == 200) { g_liked[i] = want; status(want ? "Добавлено в любимые" : "Убрано из любимых"); }
    else if (st != -1) status("Лайк: HTTP %d", st);
    PostMessageW(g_hwnd, WM_APP + 3, 1, 0);
    return 0;
}

/* ---- мелкие рисовалки ---- */
static void setr(RECT *r, int l, int t, int rr, int b) { r->left = l; r->top = t; r->right = rr; r->bottom = b; }

static void fill_rect(HDC dc, int l, int t, int r, int b, COLORREF c)
{
    RECT rc; HBRUSH hb = CreateSolidBrush(c);
    setr(&rc, l, t, r, b); FillRect(dc, &rc, hb); DeleteObject(hb);
}

static void circ(HDC dc, int cx, int cy, int r, int filled, COLORREF fc, int lw, COLORREF lc)
{
    HBRUSH hb = filled ? CreateSolidBrush(fc) : (HBRUSH)GetStockObject(NULL_BRUSH);
    HPEN hp = lw ? CreatePen(PS_SOLID, lw, lc) : (HPEN)GetStockObject(NULL_PEN);
    HGDIOBJ ob = SelectObject(dc, hb), op = SelectObject(dc, hp);
    Ellipse(dc, cx - r, cy - r, cx + r, cy + r);
    SelectObject(dc, ob); SelectObject(dc, op);
    if (filled) DeleteObject(hb);
    if (lw) DeleteObject(hp);
}

static void line2(HDC dc, int x1, int y1, int x2, int y2, int w, COLORREF c)
{
    HPEN hp = CreatePen(PS_SOLID, w, c); HGDIOBJ op = SelectObject(dc, hp);
    MoveToEx(dc, x1, y1, NULL); LineTo(dc, x2, y2);
    SelectObject(dc, op); DeleteObject(hp);
}

static void chevron(HDC dc, int cx, int cy, int s, int dir, int w, COLORREF c)
{
    int tipx = cx + dir * s / 2, tailx = cx - dir * s / 2;
    line2(dc, tailx, cy - s, tipx, cy, w, c);
    line2(dc, tipx, cy, tailx, cy + s, w, c);
}

static void poly(HDC dc, const POINT *p, int n, COLORREF fc)
{
    HBRUSH hb = CreateSolidBrush(fc); HPEN hp = CreatePen(PS_SOLID, 1, fc);
    HGDIOBJ ob = SelectObject(dc, hb), op = SelectObject(dc, hp);
    Polygon(dc, p, n);
    SelectObject(dc, ob); SelectObject(dc, op); DeleteObject(hb); DeleteObject(hp);
}

static void poly_outline(HDC dc, const POINT *p, int n, int lw, COLORREF c)
{
    HPEN hp = CreatePen(PS_SOLID, lw, c);
    HGDIOBJ ob = SelectObject(dc, GetStockObject(NULL_BRUSH)), op = SelectObject(dc, hp);
    Polygon(dc, p, n);
    SelectObject(dc, ob); SelectObject(dc, op); DeleteObject(hp);
}

static void rect_outline(HDC dc, const RECT *r, int lw, COLORREF c)
{
    POINT pt[4];
    pt[0].x = r->left;  pt[0].y = r->top;
    pt[1].x = r->right; pt[1].y = r->top;
    pt[2].x = r->right; pt[2].y = r->bottom;
    pt[3].x = r->left;  pt[3].y = r->bottom;
    poly_outline(dc, pt, 4, lw, c);
}

static void text(HDC dc, HFONT f, const WCHAR *s, int l, int t, int r, int b, COLORREF c, UINT fmt)
{
    RECT rc; HGDIOBJ of = SelectObject(dc, f);
    setr(&rc, l, t, r, b);
    SetTextColor(dc, c); SetBkMode(dc, TRANSPARENT);
    DrawTextW(dc, s, -1, &rc, fmt);
    SelectObject(dc, of);
}

static HFONT mkfont(int h, int bold)
{
    LOGFONTW lf;
    memset(&lf, 0, sizeof lf);
    lf.lfHeight = -h; lf.lfWeight = bold ? FW_BOLD : FW_NORMAL; lf.lfCharSet = DEFAULT_CHARSET;
    wcscpy(lf.lfFaceName, L"Tahoma");
    return CreateFontIndirectW(&lf);
}

static void draw_heart(HDC dc, int cx, int cy, int i, int filled, COLORREF c)
{
    POINT pt[10]; int k;
    for (k = 0; k < 10; k++) { pt[k].x = cx + HX[k] * i / 100; pt[k].y = cy + HY[k] * i / 100; }
    if (filled) poly(dc, pt, 10, c); else poly_outline(dc, pt, 10, 2, c);
}

/* значок "в начало" (dir=-1) и "вперёд" (dir=+1): планка + треугольник */
static void skip_icon(HDC dc, int cx, int cy, int s, int dir, COLORREF c)
{
    POINT t[3];
    t[0].x = cx + dir * s / 2; t[0].y = cy;
    t[1].x = cx - dir * s;     t[1].y = cy - s;
    t[2].x = cx - dir * s;     t[2].y = cy + s;
    poly(dc, t, 3, c);
    if (dir < 0) fill_rect(dc, cx - s, cy - s, cx - s * 6 / 10, cy + s, c);
    else fill_rect(dc, cx + s * 6 / 10, cy - s, cx + s, cy + s, c);
}

/* "вспышка" - значок экрана "Главное" (как в первом наброске) */
static void burst_rot(HDC dc, int cx, int cy, int R, COLORREF c, int shift)
{
    static const int cs[24] = { 100, 97, 87, 71, 50, 26, 0, -26, -50, -71, -87, -97, -100, -97, -87, -71, -50, -26, 0, 26, 50, 71, 87, 97 };
    static const int sn[24] = { 0, 26, 50, 71, 87, 97, 100, 97, 87, 71, 50, 26, 0, -26, -50, -71, -87, -97, -100, -97, -87, -71, -50, -26 };
    POINT pt[24]; int k, rr, a;
    for (k = 0; k < 24; k++) {
        rr = (k & 1) ? R * 42 / 100 : R;
        a = (k + shift) % 24;
        pt[k].x = cx + rr * cs[a] / 100; pt[k].y = cy - rr * sn[a] / 100;
    }
    poly(dc, pt, 24, c);
}

static void burst_icon(HDC dc, int cx, int cy, int R, COLORREF c) { burst_rot(dc, cx, cy, R, c, 0); }

/* анимация загрузки: пульсирующая вращающаяся вспышка на месте обложки */
static void draw_loading(HDC dc, const RECT *r)
{
    int side = r->right - r->left, ph = g_frame % 24, pulse = ph < 12 ? ph : 24 - ph, R;
    fill_rect(dc, r->left, r->top, r->right, r->bottom, K_COVER);
    R = side * (26 + pulse) / 100;
    burst_rot(dc, CXR(*r), CYR(*r), R, K_YEL, g_frame % 24);
}

/* лупа */
static void search_icon(HDC dc, int cx, int cy, int i, COLORREF c)
{
    circ(dc, cx - i / 8, cy - i / 8, i * 55 / 100, 0, 0, 3, c);
    line2(dc, cx + i * 28 / 100, cy + i * 28 / 100, cx + i * 75 / 100, cy + i * 75 / 100, 4, c);
}

/* текст песни: три строки */
static void lyrics_icon(HDC dc, int cx, int cy, int i, COLORREF c)
{
    line2(dc, cx - i, cy - i * 6 / 10, cx + i, cy - i * 6 / 10, 3, c);
    line2(dc, cx - i, cy, cx + i, cy, 3, c);
    line2(dc, cx - i, cy + i * 6 / 10, cx + i / 3, cy + i * 6 / 10, 3, c);
}

/* вывести DIB-картинку в прямоугольник с масштабированием */
static void blit_bmp(HDC dc, HBITMAP hb, int bw, int bh, int dx, int dy, int dw, int dh)
{
    HDC sd = CreateCompatibleDC(dc); HGDIOBJ ob = SelectObject(sd, hb);
    StretchBlt(dc, dx, dy, dw, dh, sd, 0, 0, bw, bh, SRCCOPY);
    SelectObject(sd, ob); DeleteDC(sd);
}

static int g_avW, g_avH;

/* круглая рамка аватара: картинка профиля (вписана в круг) или силуэт */
static void draw_avatar(HDC dc, int cx, int cy, int r)
{
    circ(dc, cx, cy, r, 1, K_COVER, 2, K_GRAY);
    if (g_hAvatar) {
        int hs = r * 70 / 100;
        blit_bmp(dc, g_hAvatar, g_avW, g_avH, cx - hs, cy - hs, 2 * hs, 2 * hs);
        circ(dc, cx, cy, r, 0, 0, 2, K_GRAY);
    } else {
        circ(dc, cx, cy - r / 4, r / 4, 1, K_GRAY, 0, 0);
        circ(dc, cx, cy + r * 55 / 100, r * 38 / 100, 1, K_GRAY, 0, 0);
    }
}

/* ---- раскладка всех экранов ---- */
static void layout_all(void)
{
    int W = g_W, H = g_H - g_sh, side, ar = W / 16, R, pcy, ph, ic = W / 11, ix, cy0;
    int pcx = W / 2;

    /* общий верхний значок (аватар на плеере, "назад" на остальных) */
    setr(&r_avatar, W / 24, H / 60, W / 24 + 2 * ar, H / 60 + 2 * ar);
    setr(&r_search, W - W / 24 - 2 * ar, H / 60, W - W / 24, H / 60 + 2 * ar);

    /* плеер */
    side = W * 68 / 100; if (side > H * 32 / 100) side = H * 32 / 100;
    R = W / 9; if (R > H * 9 / 100) R = H * 9 / 100;
    pcy = H * 61 / 100; ph = R;
    cy0 = H * 9 / 100;
    setr(&r_cover, (W - side) / 2, cy0, (W + side) / 2, cy0 + side);
    setr(&r_tt, W / 12, r_cover.bottom + H / 100, W * 11 / 12, r_cover.bottom + H * 6 / 100);
    setr(&r_ar, W / 12, r_cover.bottom + H * 6 / 100, W * 11 / 12, r_cover.bottom + H * 10 / 100);
    setr(&r_play, pcx - R, pcy - R, pcx + R, pcy + R);
    ix = pcx - R - W * 19 / 100;
    setr(&r_prev, ix - W / 9, pcy - ph, ix + W / 9, pcy + ph);
    ix = pcx + R + W * 19 / 100;
    setr(&r_next, ix - W / 9, pcy - ph, ix + W / 9, pcy + ph);
    g_sy = H * 74 / 100;
    setr(&r_dis,  W * 10 / 100 - W / 10, g_sy - W / 10, W * 10 / 100 + W / 10, g_sy + W / 10);
    setr(&r_like, W * 90 / 100 - W / 10, g_sy - W / 10, W * 90 / 100 + W / 10, g_sy + W / 10);
    /* r_prog - где ловим касание перемотки (узко, чтобы не залезать на нижние значки);
       r_progp - что перерисовывать вместе с полосой (включая время под ней) */
    setr(&r_prog,  W * 20 / 100, g_sy - H / 30, W * 80 / 100, g_sy + H / 30);
    setr(&r_progp, W * 20 / 100, g_sy - H / 40, W * 80 / 100, g_sy + H * 6 / 100);
    /* нижние значки: раньше верх их зоны (на ~13 px) попадал в зону перемотки, и касание "Главного"/"Любимого" сбивало позицию трека */
    { int ih = H * 6 / 100;
      setr(&r_home, W * 30 / 100 - ic, H * 83 / 100 - ih, W * 30 / 100 + ic, H * 83 / 100 + ih);
      setr(&r_lyr,  W * 50 / 100 - ic, H * 83 / 100 - ih, W * 50 / 100 + ic, H * 83 / 100 + ih);
      setr(&r_coll, W * 70 / 100 - ic, H * 83 / 100 - ih, W * 70 / 100 + ic, H * 83 / 100 + ih); }
    setr(&r_bar, W * 38 / 100, H * 915 / 1000, W * 62 / 100, H * 985 / 1000);

    /* главное */
    setr(&r_wave, W / 12, H * 15 / 100, W * 11 / 12, H * 41 / 100);
    setr(&r_fav,  W / 12, H * 44 / 100, W * 11 / 12, H * 64 / 100);
    setr(&r_prof, W / 12, H * 67 / 100, W * 11 / 12, H * 81 / 100);

    /* профиль */
    setr(&r_avbig, W / 2 - W / 6, H * 13 / 100, W / 2 + W / 6, H * 13 / 100 + W / 3);
    setr(&r_brep,  W / 6, H * 70 / 100, W * 5 / 6, H * 79 / 100);
    setr(&r_bexit, W / 6, H * 82 / 100, W * 5 / 6, H * 91 / 100);
}

/* верхняя полоса "назад" + название экрана по центру */
static void header(HDC dc, const WCHAR *title)
{
    int cx = CXR(r_avatar), cy = CYR(r_avatar), i = (r_avatar.right - r_avatar.left) / 2;
    circ(dc, cx, cy, i, 0, 0, 2, K_GRAY);
    chevron(dc, cx, cy, i / 3, -1, 2, K_WHITE);
    text(dc, g_fTitle, title, 0, r_avatar.top, g_W, r_avatar.bottom, K_WHITE, DT_CENTER | DT_VCENTER | DT_SINGLELINE);
}

static void paint_player(HDC dc)
{
    int W = g_W, H = g_H - g_sh, cx, cy, i, xp, y, x0, x1, side; POINT pt[10]; WCHAR tb[24]; char ab[24];
    long el = g_elapsed_ms / 1000, tot = g_total_s, pm; int playing = g_active && !g_paused;
    int liked = (g_cur >= 0 && g_cur < g_nt && g_liked[g_cur]) ? 1 : 0;
    const UINT TF = DT_CENTER | DT_VCENTER | DT_SINGLELINE | DT_END_ELLIPSIS;

    fill_rect(dc, 0, 0, W, g_H, K_BG);
    fill_rect(dc, 0, H * 90 / 100, W, g_H, K_BAR);

    /* аватар (тап = профиль) и название сервиса по центру */
    draw_avatar(dc, CXR(r_avatar), CYR(r_avatar), (r_avatar.right - r_avatar.left) / 2);
    text(dc, g_fTitle, g_wTitle, 0, r_avatar.top, W, r_avatar.bottom, K_WHITE, TF);
    search_icon(dc, CXR(r_search), CYR(r_search), (r_search.right - r_search.left) / 2, K_WHITE);

    /* обложка трека */
    side = r_cover.right - r_cover.left;
    if (g_loading) {
        draw_loading(dc, &r_cover);
    } else if (g_hCover && g_coverIdx == g_cur) {
        blit_bmp(dc, g_hCover, g_coverW, g_coverH, r_cover.left, r_cover.top, side, side);
    } else {
        fill_rect(dc, r_cover.left, r_cover.top, r_cover.right, r_cover.bottom, K_COVER);
        cx = CXR(r_cover); cy = CYR(r_cover);
        circ(dc, cx - side / 12, cy + side / 8, side / 10, 1, K_GRAY2, 0, 0);
        line2(dc, cx - side / 12 + side / 10, cy + side / 8, cx - side / 12 + side / 10, cy - side / 5, 4, K_GRAY2);
        line2(dc, cx - side / 12 + side / 10, cy - side / 5, cx + side / 8, cy - side / 8, 4, K_GRAY2);
    }

    /* название и исполнитель */
    if (g_cur >= 0 && g_cur < g_nt) {
        text(dc, g_fBig, g_ttl[g_cur], r_tt.left, r_tt.top, r_tt.right, r_tt.bottom, K_WHITE, TF);
        text(dc, g_fSmall, g_art[g_cur], r_ar.left, r_ar.top, r_ar.right, r_ar.bottom, K_GRAY, TF);
    } else if (g_loading) {
        static const char *const dots[4] = { "", ".", "..", "..." };
        sprintf(ab, "Загрузка%s", dots[(g_frame / 4) % 4]); u2w(ab, tb, 24);
        text(dc, g_fBig, tb, r_tt.left, r_tt.top, r_tt.right, r_ar.bottom, K_WHITE, TF);
    } else {
        text(dc, g_fSmall, g_wHint, r_tt.left, r_tt.top, r_tt.right, r_ar.bottom, K_GRAY, TF);
    }

    /* большая кнопка старт/пауза */
    cx = CXR(r_play); cy = CYR(r_play); i = (r_play.right - r_play.left) / 2;
    circ(dc, cx, cy, i, 1, K_YEL, 0, 0);
    if (playing) {
        fill_rect(dc, cx - i / 3, cy - i / 2, cx - i / 10, cy + i / 2, K_BG);
        fill_rect(dc, cx + i / 10, cy - i / 2, cx + i / 3, cy + i / 2, K_BG);
    } else {
        pt[0].x = cx - i / 4; pt[0].y = cy - i / 2;
        pt[1].x = cx - i / 4; pt[1].y = cy + i / 2;
        pt[2].x = cx + i / 2; pt[2].y = cy;
        poly(dc, pt, 3, K_BG);
    }
    skip_icon(dc, CXR(r_prev), CYR(r_prev), W / 22, -1, K_WHITE);
    skip_icon(dc, CXR(r_next), CYR(r_next), W / 22, 1, K_WHITE);

    /* не любимое (перечёркнутое сердце) | полоса | любимое */
    cx = CXR(r_dis); cy = CYR(r_dis); i = W / 24;
    draw_heart(dc, cx, cy, i, 0, K_GRAY);
    line2(dc, cx - i, cy - i, cx + i, cy + i, 2, K_GRAY);
    draw_heart(dc, CXR(r_like), CYR(r_like), i, liked, liked ? K_RED : K_GRAY);

    x0 = r_prog.left; x1 = r_prog.right; y = g_sy;
    pm = g_drag ? g_drag_pm : (tot > 0 ? g_elapsed_ms / tot : 0);
    if (pm < 0) pm = 0;
    if (pm > 1000) pm = 1000;
    if (g_drag && tot > 0) el = tot * pm / 1000;
    xp = x0 + (int)((long)(x1 - x0) * pm / 1000);
    line2(dc, x0, y, x1, y, 4, K_GRAY2);
    if (xp > x0) line2(dc, x0, y, xp, y, 4, K_YEL);
    circ(dc, xp, y, W / 40 + 2, 1, K_WHITE, 0, 0);
    fmt_time(el, ab); u2w(ab, tb, 24);
    text(dc, g_fSmall, tb, x0, y + H / 40, x0 + W / 4, y + H / 40 + H / 20, K_GRAY, DT_LEFT | DT_SINGLELINE);
    if (tot > 0) {
        fmt_time(tot, ab); u2w(ab, tb, 24);
        text(dc, g_fSmall, tb, x1 - W / 4, y + H / 40, x1, y + H / 40 + H / 20, K_GRAY, DT_RIGHT | DT_SINGLELINE);
    }

    /* главное (домик) и коллекция (сердце на подставке) */
    burst_icon(dc, CXR(r_home), CYR(r_home), W / 20, K_WHITE);
    lyrics_icon(dc, CXR(r_lyr), CYR(r_lyr), W / 24, K_WHITE);
    cx = CXR(r_coll); cy = CYR(r_coll); i = W / 22;
    draw_heart(dc, cx, cy - i / 4, i * 80 / 100, 0, K_WHITE);
    line2(dc, cx - i, cy + i * 70 / 100, cx - i, cy + i, 2, K_WHITE);
    line2(dc, cx - i, cy + i, cx + i, cy + i, 2, K_WHITE);
    line2(dc, cx + i, cy + i, cx + i, cy + i * 70 / 100, 2, K_WHITE);

    /* нижняя панель: кнопка старт/пауза */
    rect_outline(dc, &r_bar, 2, K_GRAY);
    cx = CXR(r_bar); cy = CYR(r_bar); i = (r_bar.bottom - r_bar.top) / 4;
    if (playing) {
        fill_rect(dc, cx - i, cy - i, cx - i / 3, cy + i, K_WHITE);
        fill_rect(dc, cx + i / 3, cy - i, cx + i, cy + i, K_WHITE);
    } else {
        pt[0].x = cx - i * 6 / 10; pt[0].y = cy - i;
        pt[1].x = cx - i * 6 / 10; pt[1].y = cy + i;
        pt[2].x = cx + i;          pt[2].y = cy;
        poly(dc, pt, 3, K_WHITE);
    }
}

/* карточка: цветной прямоугольник слева значок, справа два текста */
static void card_text(HDC dc, const RECT *r, const WCHAR *t1, const WCHAR *t2, COLORREF c1, COLORREF c2)
{
    int h = r->bottom - r->top, off = h;
    const UINT LF = DT_LEFT | DT_VCENTER | DT_SINGLELINE | DT_END_ELLIPSIS;
    text(dc, g_fBig, t1, r->left + off, r->top + h * 22 / 100, r->right - 4, r->top + h * 55 / 100, c1, LF);
    text(dc, g_fSmall, t2, r->left + off, r->top + h * 55 / 100, r->right - 4, r->top + h * 80 / 100, c2, LF);
}

static void paint_home(HDC dc)
{
    int W = g_W, cx, cy, i, k, h; char ab[48]; WCHAR tb[48];
    fill_rect(dc, 0, 0, W, g_H, K_BG);
    header(dc, g_wHome);

    /* "Моя волна": жёлтая карточка со значком-эквалайзером */
    fill_rect(dc, r_wave.left, r_wave.top, r_wave.right, r_wave.bottom, K_YEL);
    h = r_wave.bottom - r_wave.top; cx = r_wave.left + h / 2; cy = CYR(r_wave); i = h / 5;
    for (k = -2; k <= 2; k++) {
        int hh = i * (3 - (k < 0 ? -k : k)) / 3 + i / 4, bx = cx + k * i * 7 / 10;
        fill_rect(dc, bx - i / 5, cy - hh, bx + i / 5, cy + hh, K_BG);
    }
    card_text(dc, &r_wave, g_wWaveT, g_wWaveS, K_BG, K_DARK);

    /* "Любимое" */
    fill_rect(dc, r_fav.left, r_fav.top, r_fav.right, r_fav.bottom, K_BAR);
    rect_outline(dc, &r_fav, 2, K_GRAY2);
    h = r_fav.bottom - r_fav.top;
    draw_heart(dc, r_fav.left + h / 2, CYR(r_fav), h / 5, 1, K_RED);
    sprintf(ab, "Треков: %d", g_nlikes); u2w(ab, tb, 48);
    card_text(dc, &r_fav, g_wFavT, tb, K_WHITE, K_GRAY);

    /* "Профиль" */
    fill_rect(dc, r_prof.left, r_prof.top, r_prof.right, r_prof.bottom, K_BAR);
    rect_outline(dc, &r_prof, 2, K_GRAY2);
    h = r_prof.bottom - r_prof.top;
    draw_avatar(dc, r_prof.left + h / 2, CYR(r_prof), h * 36 / 100);
    card_text(dc, &r_prof, g_wProfT, g_wName[0] ? g_wName : g_wLogin, K_WHITE, K_GRAY);
}

static void paint_profile(HDC dc)
{
    int W = g_W, H = g_H - g_sh, y0; char ab[64]; WCHAR tb[64];
    const UINT TF = DT_CENTER | DT_VCENTER | DT_SINGLELINE | DT_END_ELLIPSIS;
    fill_rect(dc, 0, 0, W, g_H, K_BG);
    header(dc, g_wProfile);
    draw_avatar(dc, CXR(r_avbig), CYR(r_avbig), (r_avbig.right - r_avbig.left) / 2);

    y0 = r_avbig.bottom + H * 2 / 100;
    text(dc, g_fBig, g_wName[0] ? g_wName : g_wLogin, W / 12, y0, W * 11 / 12, y0 + H * 6 / 100, K_WHITE, TF);
    if (g_login[0]) {
        sprintf(ab, "@%s", g_login); u2w(ab, tb, 64);
        text(dc, g_fSmall, tb, W / 12, y0 + H * 6 / 100, W * 11 / 12, y0 + H * 10 / 100, K_GRAY, TF);
    }
    sprintf(ab, "Яндекс Плюс: %s", g_plus ? "подключён" : "нет"); u2w(ab, tb, 64);
    text(dc, g_fSmall, tb, W / 12, y0 + H * 11 / 100, W * 11 / 12, y0 + H * 15 / 100, g_plus ? K_YEL : K_GRAY, TF);
    sprintf(ab, "Любимых треков: %d", g_nlikes); u2w(ab, tb, 64);
    text(dc, g_fSmall, tb, W / 12, y0 + H * 15 / 100, W * 11 / 12, y0 + H * 19 / 100, K_GRAY, TF);

    fill_rect(dc, r_brep.left, r_brep.top, r_brep.right, r_brep.bottom, K_BAR);
    rect_outline(dc, &r_brep, 2, g_repeat ? K_YEL : K_GRAY2);
    sprintf(ab, "Повтор трека: %s", g_repeat ? "вкл" : "выкл"); u2w(ab, tb, 64);
    text(dc, g_fSmall, tb, r_brep.left, r_brep.top, r_brep.right, r_brep.bottom, g_repeat ? K_YEL : K_WHITE, TF);

    fill_rect(dc, r_bexit.left, r_bexit.top, r_bexit.right, r_bexit.bottom, K_BAR);
    rect_outline(dc, &r_bexit, 2, K_GRAY2);
    text(dc, g_fSmall, g_wExit, r_bexit.left, r_bexit.top, r_bexit.right, r_bexit.bottom, K_WHITE, TF);
}

static int hit(const RECT *r, int x, int y) { return x >= r->left && x < r->right && y >= r->top && y < r->bottom; }

/* расстановка стандартных элементов: список, строка поиска, окно текста песни */
static void layout_controls(void)
{
    int W = g_W, H = g_H, sh = g_sh, bh = H / 10, eh = H / 11, bw = W / 4;
    int top = (g_view == 4) ? eh : 0;
    MoveWindow(g_list, 0, top, W, H - sh - bh - top, TRUE);
    MoveWindow(g_bplay, 0, H - sh - bh, W, bh, TRUE);
    MoveWindow(g_stat, 2, H - sh, W - 4, sh, TRUE);
    MoveWindow(g_edit, 0, 0, W - bw, eh, TRUE);
    MoveWindow(g_bfind, W - bw, 0, bw, eh, TRUE);
    MoveWindow(g_lytext, 0, 0, W, H - sh - bh, TRUE);
}

/* экраны: 0 = список, 1 = плеер, 2 = главное, 3 = профиль, 4 = поиск, 5 = текст песни */
static void set_view(int v)
{
    g_view = v;
    if (v == 0) likes_fill();            /* "Любимое": отдельный слой, играющую очередь не трогает */
    else if (v == 4) list_rebuild();     /* поиск: список = текущая очередь (результаты поиска) */
    ShowWindow(g_list, (v == 0 || v == 4) ? SW_SHOW : SW_HIDE);
    ShowWindow(g_bplay, (v == 0 || v == 4 || v == 5) ? SW_SHOW : SW_HIDE);
    ShowWindow(g_edit, v == 4 ? SW_SHOW : SW_HIDE);
    ShowWindow(g_bfind, v == 4 ? SW_SHOW : SW_HIDE);
    ShowWindow(g_lytext, v == 5 ? SW_SHOW : SW_HIDE);
    layout_controls();
    SetFocus(v == 0 ? g_list : v == 4 ? g_edit : v == 5 ? g_lytext : g_hwnd);
    InvalidateRect(g_hwnd, NULL, TRUE);
}

static void toggle_play(void)
{
    if (g_active && g_hwo) {
        if (g_paused) { waveOutRestart(g_hwo); g_paused = 0; }
        else { waveOutPause(g_hwo); g_paused = 1; }
        InvalidateRect(g_hwnd, NULL, FALSE);
    } else if (g_nt) {
        int s = g_listkind == 1 ? (int)SendMessageW(g_list, LB_GETCURSEL, 0, 0) : g_cur;
        play_idx(s >= 0 ? s : 0);
    }
}

static void like_cur(int want)
{
    if (g_cur >= 0 && g_cur < g_nt) {
        HANDLE t = CreateThread(NULL, 0, like_thread, (LPVOID)(size_t)((g_cur << 1) | want), 0, NULL);
        if (t) CloseHandle(t);
    }
}

/* "Любимое" - просто переход на другой слой: музыка продолжает играть, очередь не меняется */
static void open_likes_view(void)
{
    set_view(0);
    status("Любимое: %d", likes_count());
}

/* двойной тап по треку на экране "Любимое": только теперь очередь становится списком любимых */
static void play_from_likes(int s)
{
    if (s < 0 || s >= likes_count()) return;
    if (g_mode != 0) {                       /* играла волна/поиск - возвращаем любимые */
        g_pending = -2; SetEvent(g_ev);
        queue_restore(); g_mode = 0; g_coverIdx = -1;
    }
    g_cur = s;
    list_rebuild();
    play_idx(s);
    set_view(1);
}

static void open_lyrics(void)
{
    HANDLE t;
    if (g_cur < 0 || g_cur >= g_nt) { status("Сначала выберите трек"); return; }
    SetWindowTextW(g_lytext, g_wLyrLoad);
    set_view(5);
    t = CreateThread(NULL, 0, lyrics_thread, (LPVOID)(size_t)g_cur, 0, NULL);
    if (t) CloseHandle(t);
}

static void start_wave(void)
{
    HANDLE t = CreateThread(NULL, 0, wave_thread, NULL, 0, NULL);
    if (t) CloseHandle(t);
    set_view(1);
}

static HBITMAP make_dib(const CoverImg *ci)
{
    BITMAPINFO bi; void *bits = NULL; HBITMAP hb; HDC sdc; int stride, x, y;
    memset(&bi, 0, sizeof bi);
    bi.bmiHeader.biSize = sizeof(BITMAPINFOHEADER);
    bi.bmiHeader.biWidth = ci->w; bi.bmiHeader.biHeight = ci->h;   /* строки снизу вверх */
    bi.bmiHeader.biPlanes = 1; bi.bmiHeader.biBitCount = 24; bi.bmiHeader.biCompression = BI_RGB;
    sdc = GetDC(g_hwnd);
    hb = CreateDIBSection(sdc, &bi, DIB_RGB_COLORS, &bits, NULL, 0);
    ReleaseDC(g_hwnd, sdc);
    if (!hb || !bits) { if (hb) DeleteObject(hb); return NULL; }
    stride = (ci->w * 3 + 3) & ~3;
    for (y = 0; y < ci->h; y++) {
        const unsigned char *s = ci->rgb + (size_t)(ci->h - 1 - y) * ci->w * 3;
        unsigned char *d = (unsigned char *)bits + (size_t)y * stride;
        for (x = 0; x < ci->w; x++) { d[3 * x] = s[3 * x + 2]; d[3 * x + 1] = s[3 * x + 1]; d[3 * x + 2] = s[3 * x]; }
    }
    return hb;
}

static void on_tap(int x, int y)
{
    if (g_view == 1) {
        if (hit(&r_avatar, x, y)) set_view(3);
        else if (hit(&r_play, x, y) || hit(&r_bar, x, y)) toggle_play();
        else if (hit(&r_prev, x, y)) { if (g_cur > 0) play_idx(g_cur - 1); }
        else if (hit(&r_next, x, y)) { if (g_cur + 1 < g_nt) play_idx(g_cur + 1); }
        else if (hit(&r_dis, x, y)) like_cur(0);
        else if (hit(&r_like, x, y)) like_cur(1);
        else if (hit(&r_home, x, y)) set_view(2);
        else if (hit(&r_lyr, x, y)) open_lyrics();
        else if (hit(&r_search, x, y)) set_view(4);
        else if (hit(&r_coll, x, y)) open_likes_view();
    } else if (g_view == 2) {
        if (hit(&r_avatar, x, y)) set_view(1);
        else if (hit(&r_wave, x, y)) { if (g_mode == 1 && g_nt > 0) set_view(1); else start_wave(); }   /* волна уже играет - просто к плееру */
        else if (hit(&r_fav, x, y)) open_likes_view();
        else if (hit(&r_prof, x, y)) set_view(3);
    } else if (g_view == 3) {
        if (hit(&r_avatar, x, y)) set_view(1);
        else if (hit(&r_brep, x, y)) { g_repeat = !g_repeat; InvalidateRect(g_hwnd, NULL, FALSE); }
        else if (hit(&r_bexit, x, y)) DestroyWindow(g_hwnd);
    }
}

static LRESULT CALLBACK wndproc(HWND h, UINT m, WPARAM w, LPARAM l)
{
    switch (m) {
    case WM_CREATE:
        g_hwnd = h;
        g_brBg = CreateSolidBrush(K_BG);
        u2w("Я.Музыка", g_wTitle, 16);
        u2w("Нажмите старт, чтобы играть любимые", g_wHint, 40);
        u2w("Главное", g_wHome, 16);
        u2w("Моя волна", g_wWaveT, 24);
        u2w("Музыка под ваше настроение", g_wWaveS, 40);
        u2w("Любимое", g_wFavT, 24);
        u2w("Профиль", g_wProfT, 24);
        u2w("Профиль", g_wProfile, 16);
        u2w("Выход", g_wExit, 16);
        u2w("Загрузка текста...", g_wLyrLoad, 32);
        u2w("Найти", g_wFind, 16);
        g_list = CreateWindowW(L"LISTBOX", L"", WS_CHILD | WS_VISIBLE | WS_VSCROLL | LBS_NOTIFY,
                               0, 0, 10, 10, h, (HMENU)ID_LIST, 0, 0);
        g_stat = CreateWindowW(L"STATIC", L"", WS_CHILD | WS_VISIBLE, 0, 0, 10, 10, h, 0, 0, 0);
        { WCHAR t[24]; u2w("К плееру", t, 24);
          g_bplay = CreateWindowW(L"BUTTON", t, WS_CHILD | WS_VISIBLE, 0, 0, 10, 10, h, (HMENU)ID_TOPLAY, 0, 0); }
        g_edit = CreateWindowW(L"EDIT", L"", WS_CHILD | WS_BORDER | ES_AUTOHSCROLL, 0, 0, 10, 10, h, (HMENU)ID_EDIT, 0, 0);
        g_bfind = CreateWindowW(L"BUTTON", g_wFind, WS_CHILD, 0, 0, 10, 10, h, (HMENU)ID_FIND, 0, 0);
        g_lytext = CreateWindowW(L"EDIT", L"", WS_CHILD | WS_VSCROLL | ES_MULTILINE | ES_READONLY | ES_AUTOVSCROLL,
                                 0, 0, 10, 10, h, (HMENU)ID_LYR, 0, 0);
        set_view(1);   /* сразу открываем плеер */
        SetTimer(h, 1, 90, NULL);   /* кадры анимации загрузки */
        return 0;
    case WM_SIZE: {
        int W = LOWORD(l), H = HIWORD(l), sh, bh;
        g_W = W; g_H = H; sh = H / 16; if (sh < 18) sh = 18; g_sh = sh; bh = H / 10;
        (void)bh;
        if (g_fTitle) DeleteObject(g_fTitle);
        if (g_fBig) DeleteObject(g_fBig);
        if (g_fSmall) DeleteObject(g_fSmall);
        g_fTitle = mkfont(H / 24 + 4, 1); g_fBig = mkfont(H / 26 + 4, 1); g_fSmall = mkfont(H / 32 + 2, 0);
        layout_all();
        layout_controls();
        InvalidateRect(h, NULL, TRUE);
        return 0; }
    case WM_ERASEBKGND:
        return 1;
    case WM_PAINT: {
        PAINTSTRUCT ps; RECT rc; HDC dc = BeginPaint(h, &ps);
        rc = ps.rcPaint;
        if (g_view >= 1 && g_view <= 3 && rc.right > rc.left && rc.bottom > rc.top) {
            int bw = rc.right - rc.left, bh = rc.bottom - rc.top;
            HDC md = CreateCompatibleDC(dc); HBITMAP bm = CreateCompatibleBitmap(dc, bw, bh);
            HGDIOBJ ob = SelectObject(md, bm);
            SetViewportOrgEx(md, -rc.left, -rc.top, NULL);
            if (g_view == 1) paint_player(md);
            else if (g_view == 2) paint_home(md);
            else paint_profile(md);
            BitBlt(dc, rc.left, rc.top, bw, bh, md, rc.left, rc.top, SRCCOPY);
            SelectObject(md, ob); DeleteObject(bm); DeleteDC(md);
        } else {
            fill_rect(dc, rc.left, rc.top, rc.right, rc.bottom, K_BG);
        }
        EndPaint(h, &ps);
        return 0; }
    case WM_CTLCOLORSTATIC:
    case WM_CTLCOLORLISTBOX:
    case WM_CTLCOLOREDIT:
        SetTextColor((HDC)w, K_WHITE); SetBkColor((HDC)w, K_BG);
        return (LRESULT)g_brBg;
    case WM_LBUTTONDOWN: {
        int x = (short)LOWORD(l), y = (short)HIWORD(l);
        if (g_view == 1 && g_total_s > 0 && hit(&r_prog, x, y)) {
            long pm = (long)(x - r_prog.left) * 1000 / (r_prog.right - r_prog.left);
            if (pm < 0) pm = 0;
            if (pm > 1000) pm = 1000;
            g_drag = 1; g_drag_pm = (int)pm; SetCapture(h);
            InvalidateRect(h, &r_progp, FALSE);
        } else if (g_view >= 1 && g_view <= 3) on_tap(x, y);
        return 0; }
    case WM_MOUSEMOVE:
        if (g_drag) {
            long pm = (long)((short)LOWORD(l) - r_prog.left) * 1000 / (r_prog.right - r_prog.left);
            if (pm < 0) pm = 0;
            if (pm > 1000) pm = 1000;
            g_drag_pm = (int)pm; InvalidateRect(h, &r_progp, FALSE);
        }
        return 0;
    case WM_LBUTTONUP:
        if (g_drag) {
            g_drag = 0; ReleaseCapture();
            g_seek_pm = g_drag_pm;          /* команда плееру: перемотать */
            InvalidateRect(h, &r_progp, FALSE);
        }
        return 0;
    case WM_KEYDOWN:
        if (g_view == 1) {
            if (w == VK_LEFT) { if (g_cur > 0) play_idx(g_cur - 1); }
            else if (w == VK_RIGHT) { if (g_cur + 1 < g_nt) play_idx(g_cur + 1); }
            else if (w == VK_RETURN) toggle_play();
            else if (w == VK_ESCAPE) set_view(2);
        } else if (g_view >= 2 && w == VK_ESCAPE) set_view(1);
        return 0;
    case WM_COMMAND:
        switch (LOWORD(w)) {
        case ID_LIST:
            if (HIWORD(w) == LBN_DBLCLK) {
                int s = (int)SendMessageW(g_list, LB_GETCURSEL, 0, 0);
                if (s >= 0) {
                    if (g_view == 0) play_from_likes(s);
                    else { g_cur = s; play_idx(s); set_view(1); }
                }
            }
            break;
        case ID_TOPLAY: set_view(1); break;
        case ID_FIND: {
            WCHAR wq[128]; char *q; int nb;
            GetWindowTextW(g_edit, wq, 128);
            if (!wq[0]) break;
            q = (char *)malloc(400);
            if (!q) break;
            nb = WideCharToMultiByte(CP_UTF8, 0, wq, -1, q, 399, NULL, NULL);
            if (nb <= 0) { free(q); break; }
            q[399] = 0;
            { HANDLE t = CreateThread(NULL, 0, search_thread, q, 0, NULL); if (t) CloseHandle(t); else free(q); }
            break; }
        }
        return 0;
    case WM_APP + 2:   /* начался новый трек */
        if (g_listkind == 1) SendMessageW(g_list, LB_SETCURSEL, w, 0);
        if ((int)w != g_coverIdx) {
            if (g_hCover) { DeleteObject(g_hCover); g_hCover = NULL; }
            g_coverIdx = -1;
        }
        if (g_view >= 1) InvalidateRect(h, NULL, FALSE);
        return 0;
    case WM_APP + 3:   /* w=0: обновить полосу, w=1: перерисовать всё */
        if (g_view == 1) InvalidateRect(h, w ? NULL : &r_progp, FALSE);
        else if (g_view >= 2 && w) InvalidateRect(h, NULL, FALSE);
        return 0;
    case WM_APP + 4: { /* пришла обложка трека */
        CoverImg *ci = (CoverImg *)l;
        if (ci) {
            if ((int)w == g_cur) {
                HBITMAP hb = make_dib(ci);
                if (hb) {
                    if (g_hCover) DeleteObject(g_hCover);
                    g_hCover = hb; g_coverW = ci->w; g_coverH = ci->h; g_coverIdx = (int)w;
                    if (g_view == 1) InvalidateRect(h, &r_cover, FALSE);
                }
            }
            stbi_image_free(ci->rgb); free(ci);
        }
        return 0; }
    case WM_APP + 6: { /* пришёл аватар профиля */
        CoverImg *ci = (CoverImg *)l;
        if (ci) {
            HBITMAP hb = make_dib(ci);
            if (hb) {
                if (g_hAvatar) DeleteObject(g_hAvatar);
                g_hAvatar = hb; g_avW = ci->w; g_avH = ci->h;
                if (g_view >= 1) InvalidateRect(h, NULL, FALSE);
            }
            stbi_image_free(ci->rgb); free(ci);
        }
        return 0; }
    case WM_TIMER:     /* кадры анимации загрузки */
        if (w == 1) {
            if (g_loading) {
                g_frame++;
                if ((g_elapsed_ms > 0 && g_active) || g_frame > 700) g_loading = 0;
            }
            if (g_loading) {
                if (g_view == 1) {
                    RECT ir; ir.left = r_cover.left; ir.top = r_cover.top; ir.right = r_cover.right; ir.bottom = r_ar.bottom;
                    InvalidateRect(h, &ir, FALSE);
                }
            } else {
                KillTimer(h, 1);
                InvalidateRect(h, NULL, FALSE);
            }
        }
        return 0;
    case WM_APP + 8:   /* загрузка закончилась (или не удалась) */
        g_loading = 0;
        return 0;
    case WM_ACTIVATE:
        if (LOWORD(w) != WA_INACTIVE) {       /* вернулись в приложение: показываем актуальное состояние */
            if (g_listkind == 1 && g_cur >= 0 && g_cur < g_nt) SendMessageW(g_list, LB_SETCURSEL, g_cur, 0);
            if (g_cur >= 0 && g_cur < g_nt && g_coverIdx != g_cur) {
                HANDLE ch = CreateThread(NULL, 0, cover_thread, (LPVOID)(size_t)g_cur, 0, NULL);
                if (ch) CloseHandle(ch);
            }
            InvalidateRect(h, NULL, FALSE);
        }
        break;
    case WM_APP + 9:   /* поиск завершён: показать список результатов */
        SendMessageW(g_list, LB_SETCURSEL, 0, 0);
        SetFocus(g_list);
        return 0;
    case WM_APP + 7: { /* пришёл текст песни */
        WCHAR *txt = (WCHAR *)l;
        if (txt) { SetWindowTextW(g_lytext, txt); free(txt); }
        return 0; }
    case WM_DESTROY:
        PostQuitMessage(0); return 0;
    }
    return DefWindowProcW(h, m, w, l);
}

int WINAPI WinMain(HINSTANCE hi, HINSTANCE hp, LPWSTR cmd, int show)
{
    WNDCLASSW wc; MSG msg;
    HANDLE mtx; HWND old;
    (void)hp; (void)cmd;
    /* Один экземпляр: если приложение уже запущено (свернули крестиком), просто возвращаем его на экран -
       иначе второй запуск начинал бы вторую параллельную музыку */
    mtx = CreateMutexW(NULL, FALSE, L"YMP_single_instance");
    if (mtx && GetLastError() == ERROR_ALREADY_EXISTS) {
        old = FindWindowW(L"YMP", NULL);
        if (old) { ShowWindow(old, SW_SHOW); SetForegroundWindow((HWND)((ULONG)old | 0x01)); }
        return 0;
    }
    InitializeCriticalSection(&g_cs);
    InitializeCriticalSection(&g_hcs);
    load_config();
    hist_load();
    g_ev = CreateEventW(NULL, FALSE, FALSE, NULL);
    memset(&wc, 0, sizeof wc);
    wc.lpfnWndProc = wndproc; wc.hInstance = hi; wc.lpszClassName = L"YMP";
    wc.hbrBackground = (HBRUSH)GetStockObject(BLACK_BRUSH);
    RegisterClassW(&wc);
    g_hwnd = CreateWindowW(L"YMP", L"YMusic", WS_VISIBLE | WS_CLIPCHILDREN, CW_USEDEFAULT, CW_USEDEFAULT,
                           CW_USEDEFAULT, CW_USEDEFAULT, 0, 0, hi, 0);
    ShowWindow(g_hwnd, show); UpdateWindow(g_hwnd);
    CreateThread(NULL, 0, loader_thread, NULL, 0, NULL);
    while (GetMessageW(&msg, 0, 0, 0)) { TranslateMessage(&msg); DispatchMessageW(&msg); }
    ExitProcess(0);
    return 0;
}
