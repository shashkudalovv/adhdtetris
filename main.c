#define _POSIX_C_SOURCE 200809L

#include <CoreGraphics/CoreGraphics.h>
#include <objc/message.h>
#include <objc/runtime.h>

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

enum {
    COLS = 10, ROWS = 20, PIECES = 7,
    MAX_PARTICLES = 1400, MAX_WAVES = 64, MAX_SCORE_POPUPS = 160
};
enum {
    SPECIAL_NONE, SPECIAL_BOMB, SPECIAL_LASER, SPECIAL_ROCKET,
    SPECIAL_CROSS, SPECIAL_PRISM, SPECIAL_METEOR,
    SPECIAL_DIAGONAL, SPECIAL_DRILL, SPECIAL_PULSE, SPECIAL_THUNDER
};

static const int WINDOW_W = 670;
static const int WINDOW_H = 720;
static const int CELL = 30;
static const int BOARD_X = 55;
static const int BOARD_Y = 60;

typedef struct { int x, y; } Block;
typedef struct {
    int type, rotation, x, y;
    int special_index, special_type;
} FallingPiece;
typedef struct { double r, g, b; } Color;
typedef struct {
    double x, y, vx, vy, life, max_life, size;
    Color color;
    bool active;
} Particle;
typedef struct {
    double x, y, life, max_life;
    int type, variant;
    bool active;
} Shockwave;
typedef struct {
    double y;
    int column, mode;
    bool active;
} Rocket;
typedef struct {
    double x, y, vy, life, max_life;
    int points;
    Color color;
    bool active;
} ScorePopup;

static int board[ROWS][COLS];
static unsigned char board_special[ROWS][COLS];
static unsigned char effect_kind[ROWS][COLS];
static unsigned char effect_variant[ROWS][COLS];
static double effect_timer[ROWS][COLS];
static double fall_offset[ROWS][COLS];
static FallingPiece current;
static int next_piece;
static int next_special_index;
static int next_special_type;
static int bag[PIECES];
static int bag_pos = PIECES;
static int score;
static int lines;
static int level;
static int high_score;
static bool high_score_dirty;
static bool paused;
static bool game_over;
static bool running = true;
static double gravity_accumulator;
static double elapsed_time;
static double visual_time;
static double shake_time;
static double shake_strength;
static double flash_time;
static int flash_kind;
static double settle_accumulator;
static bool waiting_for_settle;
static bool last_clear_started_physics;
static bool normal_clear_active;
static bool pending_clear_rows[ROWS];
static double normal_clear_timer;
static int pending_clear_count;
static int normal_clear_variant;
static int meteor_shower_remaining;
static int cascade_chain;
static double chain_display_timer;
static double focus_charge;
static double focus_time;
static double danger_event_timer;
static double danger_flash_time;
static double board_rise_offset;
static double perfect_clear_timer;
static bool perfect_clear_candidate;
static double overdrive_time;
static double overdrive_banner_timer;
static int flow_streak;
static double flow_display_timer;
static bool rescue_shield;
static int next_shield_lines;
static double shield_banner_timer;
static double minecraft_time;
static double minecraft_banner_timer;
static double minecraft_flash_time;
static ScorePopup score_popups[MAX_SCORE_POPUPS];
static int score_popup_cursor;
static Particle particles[MAX_PARTICLES];
static Shockwave shockwaves[MAX_WAVES];
static Rocket rocket;
static int particle_cursor;
static int wave_cursor;

/* I, O, T, S, Z, J, L -- four rotations, four blocks each. */
static const Block shapes[PIECES][4][4] = {
    {
        {{0,1},{1,1},{2,1},{3,1}}, {{2,0},{2,1},{2,2},{2,3}},
        {{0,2},{1,2},{2,2},{3,2}}, {{1,0},{1,1},{1,2},{1,3}}
    },
    {
        {{1,0},{2,0},{1,1},{2,1}}, {{1,0},{2,0},{1,1},{2,1}},
        {{1,0},{2,0},{1,1},{2,1}}, {{1,0},{2,0},{1,1},{2,1}}
    },
    {
        {{1,0},{0,1},{1,1},{2,1}}, {{1,0},{1,1},{2,1},{1,2}},
        {{0,1},{1,1},{2,1},{1,2}}, {{1,0},{0,1},{1,1},{1,2}}
    },
    {
        {{1,0},{2,0},{0,1},{1,1}}, {{1,0},{1,1},{2,1},{2,2}},
        {{1,1},{2,1},{0,2},{1,2}}, {{0,0},{0,1},{1,1},{1,2}}
    },
    {
        {{0,0},{1,0},{1,1},{2,1}}, {{2,0},{1,1},{2,1},{1,2}},
        {{0,1},{1,1},{1,2},{2,2}}, {{1,0},{0,1},{1,1},{0,2}}
    },
    {
        {{0,0},{0,1},{1,1},{2,1}}, {{1,0},{2,0},{1,1},{1,2}},
        {{0,1},{1,1},{2,1},{2,2}}, {{1,0},{1,1},{0,2},{1,2}}
    },
    {
        {{2,0},{0,1},{1,1},{2,1}}, {{1,0},{1,1},{1,2},{2,2}},
        {{0,1},{1,1},{2,1},{0,2}}, {{0,0},{1,0},{1,1},{1,2}}
    }
};

static const Color piece_colors[PIECES + 1] = {
    {0.0, 0.0, 0.0}, {0.12, 0.82, 0.94}, {0.98, 0.82, 0.18},
    {0.68, 0.30, 0.90}, {0.27, 0.82, 0.38}, {0.94, 0.25, 0.32},
    {0.22, 0.42, 0.94}, {1.00, 0.52, 0.15}
};

static double random_unit(void) {
    return (double)rand() / (double)RAND_MAX;
}

static bool get_high_score_path(char *path, size_t capacity, bool temporary) {
    const char *user_home = getenv("HOME");
    if (!user_home || !user_home[0]) return false;
    int length = snprintf(path, capacity, "%s/.adhdtetris_highscore%s",
                          user_home, temporary ? ".tmp" : "");
    return length > 0 && (size_t)length < capacity;
}

static void load_high_score(void) {
    char path[1024];
    if (!get_high_score_path(path, sizeof(path), false)) return;
    FILE *file = fopen(path, "r");
    if (!file) return;
    int saved_score = 0;
    if (fscanf(file, "%d", &saved_score) == 1 && saved_score > 0)
        high_score = saved_score;
    fclose(file);
}

static void save_high_score(void) {
    if (!high_score_dirty) return;
    char path[1024], temporary_path[1024];
    if (!get_high_score_path(path, sizeof(path), false) ||
        !get_high_score_path(temporary_path, sizeof(temporary_path), true))
        return;
    FILE *file = fopen(temporary_path, "w");
    if (!file) return;
    bool written = fprintf(file, "%d\n", high_score) > 0;
    if (fclose(file) != 0) written = false;
    if (written && rename(temporary_path, path) == 0)
        high_score_dirty = false;
    else
        unlink(temporary_path);
}

static void start_minecraft_event(void) {
    minecraft_time = 20.0;
    minecraft_banner_timer = 2.6;
    minecraft_flash_time = 0.45;
    shake_time = 0.42;
    if (shake_strength < 9.0) shake_strength = 9.0;
    for (int i = 0; i < 84; ++i) {
        Particle *p = &particles[particle_cursor++ % MAX_PARTICLES];
        p->active = true;
        p->x = BOARD_X + random_unit() * COLS * CELL;
        p->y = BOARD_Y + ROWS * CELL * 0.45 +
               (random_unit() - 0.5) * 90.0;
        p->vx = (random_unit() - 0.5) * 260.0;
        p->vy = 100.0 + random_unit() * 280.0;
        p->max_life = 0.55 + random_unit() * 0.55;
        p->life = p->max_life;
        p->size = 4.0 + random_unit() * 7.0;
        p->color = i % 3 == 0 ? (Color){0.24, 0.68, 0.16}
                              : (Color){0.46, 0.27, 0.12};
    }
}

static void start_special_impact(int x, int y, int special, int variant) {
    Shockwave *wave = &shockwaves[wave_cursor++ % MAX_WAVES];
    wave->active = true;
    wave->x = BOARD_X + (x + 0.5) * CELL;
    wave->y = BOARD_Y + (ROWS - y - 0.5) * CELL;
    wave->max_life = special == SPECIAL_ROCKET ? 0.62
        : (special == SPECIAL_METEOR ? 0.50
        : (special == SPECIAL_BOMB ? 0.44
        : (special == SPECIAL_PRISM ? 0.52
        : (special == SPECIAL_PULSE ? 0.48
        : (special == SPECIAL_THUNDER ? 0.42 : 0.34)))));
    wave->life = wave->max_life;
    wave->type = special;
    wave->variant = variant;

    double power = special == SPECIAL_ROCKET ? 20.0
        : (special == SPECIAL_METEOR ? 16.0
        : (special == SPECIAL_BOMB ? 18.0
        : (special == SPECIAL_PRISM ? 13.0
        : (special == SPECIAL_PULSE ? 14.5
        : (special == SPECIAL_THUNDER ? 12.5 : 11.0)))));
    if (shake_strength < power) shake_strength = power;
    else shake_strength += 2.2;
    if (shake_strength > 22.0) shake_strength = 22.0;
    shake_time = special == SPECIAL_ROCKET ? 0.58
        : (special == SPECIAL_METEOR ? 0.48
        : (special == SPECIAL_BOMB ? 0.52
        : (special == SPECIAL_PULSE ? 0.44 : 0.36)));
    flash_time = special == SPECIAL_ROCKET ? 0.28
        : (special == SPECIAL_METEOR ? 0.24
        : (special == SPECIAL_BOMB ? 0.25
        : (special == SPECIAL_PRISM ? 0.26
        : (special == SPECIAL_PULSE ? 0.23 : 0.20))));
    flash_kind = special;

    Color spark = {0.55, 0.95, 1.0};
    if (special == SPECIAL_BOMB || special == SPECIAL_ROCKET)
        spark = (Color){1.0, 0.52, 0.08};
    else if (special == SPECIAL_METEOR || special == SPECIAL_PRISM)
        spark = (Color){0.82, 0.42, 1.0};
    else if (special == SPECIAL_PULSE)
        spark = (Color){1.0, 0.88, 0.16};
    else if (special == SPECIAL_DIAGONAL)
        spark = (Color){0.32, 1.0, 0.55};
    for (int i = 0; i < 30; ++i) {
        Particle *p = &particles[particle_cursor++ % MAX_PARTICLES];
        p->active = true;
        p->x = wave->x + (random_unit() - 0.5) * 10.0;
        p->y = wave->y + (random_unit() - 0.5) * 10.0;
        double direction_x = random_unit() - 0.5;
        double direction_y = random_unit() - 0.5;
        double burst = 280.0 + random_unit() * 340.0;
        p->vx = direction_x * burst;
        p->vy = direction_y * burst + 90.0;
        p->max_life = 0.30 + random_unit() * 0.34;
        p->life = p->max_life;
        p->size = 2.0 + random_unit() * 4.5;
        p->color = i % 4 == 0 ? (Color){1.0, 1.0, 1.0} : spark;
    }
}

static void spawn_fragments(int x, int y, int color_index, int special,
                            int source_x, int source_y) {
    if (color_index <= 0 || color_index > PIECES) return;
    double center_x = BOARD_X + (x + 0.5) * CELL;
    double center_y = BOARD_Y + (ROWS - y - 0.5) * CELL;
    int fragment_count = special == SPECIAL_ROCKET ? 22
        : (special == SPECIAL_METEOR ? 18 : 14);
    for (int i = 0; i < fragment_count; ++i) {
        Particle *p = &particles[particle_cursor++ % MAX_PARTICLES];
        p->active = true;
        p->x = center_x + (random_unit() - 0.5) * 18.0;
        p->y = center_y + (random_unit() - 0.5) * 18.0;
        if (special == SPECIAL_BOMB || special == SPECIAL_ROCKET ||
            special == SPECIAL_METEOR || special == SPECIAL_PRISM ||
            special == SPECIAL_PULSE || special == SPECIAL_THUNDER) {
            double force = special == SPECIAL_ROCKET ? 205.0
                : (special == SPECIAL_METEOR ? 180.0 : 145.0);
            double scatter = special == SPECIAL_ROCKET ? 350.0
                : (special == SPECIAL_METEOR ? 310.0 : 255.0);
            p->vx = (x - source_x) * force +
                    (random_unit() - 0.5) * scatter;
            p->vy = -(y - source_y) * force + 70.0 +
                    (random_unit() - 0.5) * scatter;
        } else {
            p->vx = (random_unit() - 0.5) * 220.0;
            p->vy = 150.0 + random_unit() * 280.0;
        }
        p->max_life = 0.52 + random_unit() * 0.38;
        p->life = p->max_life;
        p->size = 3.0 + random_unit() * 6.5;
        p->color = piece_colors[color_index];
    }
}

static void spawn_line_fragments(int x, int y, int color_index) {
    double center_x = BOARD_X + (x + 0.5) * CELL;
    double center_y = BOARD_Y + (ROWS - y - 0.5) * CELL;
    for (int i = 0; i < 5; ++i) {
        Particle *p = &particles[particle_cursor++ % MAX_PARTICLES];
        p->active = true;
        p->x = center_x + (random_unit() - 0.5) * 18.0;
        p->y = center_y + (random_unit() - 0.5) * 12.0;
        p->vx = (random_unit() - 0.5) * 105.0;
        p->vy = 35.0 + random_unit() * 90.0;
        p->max_life = 0.30 + random_unit() * 0.24;
        p->life = p->max_life;
        p->size = 2.0 + random_unit() * 3.5;
        p->color = piece_colors[color_index];
    }
}

static void spawn_score_popup(double x, double y, int points, Color color) {
    ScorePopup *popup = &score_popups[score_popup_cursor++ % MAX_SCORE_POPUPS];
    popup->active = true;
    popup->x = x;
    popup->y = y;
    popup->vy = 46.0;
    popup->max_life = 1.05;
    popup->life = popup->max_life;
    popup->points = points;
    popup->color = color;
}

static void spawn_cell_score(int x, int y, int points, Color color) {
    spawn_score_popup(BOARD_X + (x + 0.5) * CELL,
                      BOARD_Y + (ROWS - y - 0.5) * CELL,
                      points, color);
}

static int award_points(int base_points) {
    int multiplier = overdrive_time > 0.0 ? 3 : (focus_time > 0.0 ? 2 : 1);
    if (minecraft_time > 0.0) multiplier *= 2;
    int awarded = base_points * multiplier;
    score += awarded;
    if (score > high_score) {
        high_score = score;
        high_score_dirty = true;
    }
    return awarded;
}

static void add_focus_charge(double amount) {
    if (focus_time > 0.0) return;
    focus_charge += amount;
    if (focus_charge > 100.0) focus_charge = 100.0;
}

static void check_perfect_clear(void) {
    if (!perfect_clear_candidate) return;
    for (int y = 0; y < ROWS; ++y)
        for (int x = 0; x < COLS; ++x)
            if (board[y][x]) return;
    int bonus = award_points(2000 * level);
    add_focus_charge(40.0);
    spawn_score_popup(BOARD_X + COLS * CELL / 2.0,
                      BOARD_Y + ROWS * CELL / 2.0,
                      bonus, (Color){1.0, 0.86, 0.24});
    perfect_clear_timer = 1.8;
    rescue_shield = true;
    shield_banner_timer = 2.0;
    perfect_clear_candidate = false;
}

static bool activate_rescue_shield(void) {
    if (!rescue_shield) return false;
    rescue_shield = false;
    shield_banner_timer = 2.2;
    start_special_impact(COLS / 2, 2, SPECIAL_THUNDER, 2);
    flash_time = 0.34;
    flash_kind = SPECIAL_THUNDER;
    shake_time = 0.58;
    if (shake_strength < 15.0) shake_strength = 15.0;
    for (int y = 0; y < 5; ++y) {
        for (int x = 0; x < COLS; ++x) {
            effect_kind[y][x] = SPECIAL_THUNDER;
            effect_variant[y][x] = (unsigned char)((x + y) % 3);
            effect_timer[y][x] = 0.62;
            if (board[y][x])
                spawn_fragments(x, y, board[y][x], SPECIAL_THUNDER,
                                COLS / 2, 2);
            board[y][x] = 0;
            board_special[y][x] = SPECIAL_NONE;
            fall_offset[y][x] = 0.0;
        }
    }
    return true;
}

static void trigger_garbage_surge(void) {
    danger_event_timer = 1.6;
    danger_flash_time = 0.22;
    shake_time = 0.34;
    if (shake_strength < 8.0) shake_strength = 8.0;
    for (int x = 0; x < COLS; ++x) {
        if (board[0][x]) {
            if (!activate_rescue_shield()) {
                game_over = true;
                return;
            }
            break;
        }
    }
    for (int y = 0; y < ROWS - 1; ++y) {
        memcpy(board[y], board[y + 1], sizeof(board[y]));
        memcpy(board_special[y], board_special[y + 1], sizeof(board_special[y]));
    }
    int hole_a = rand() % COLS;
    int hole_b;
    do { hole_b = rand() % COLS; } while (hole_b == hole_a);
    for (int x = 0; x < COLS; ++x) {
        board[ROWS - 1][x] = (x == hole_a || x == hole_b)
            ? 0 : 1 + rand() % PIECES;
        board_special[ROWS - 1][x] = SPECIAL_NONE;
        if (board[ROWS - 1][x])
            spawn_line_fragments(x, ROWS - 1, board[ROWS - 1][x]);
    }
    memset(fall_offset, 0, sizeof(fall_offset));
    board_rise_offset = -CELL;
}

static int draw_from_bag(void);
static void roll_special(int *index, int *type);

static int random_special_type(void) {
    int roll = rand() % 100;
    if (roll < 12) return SPECIAL_BOMB;
    if (roll < 32) return SPECIAL_LASER;
    if (roll < 45) return SPECIAL_CROSS;
    if (roll < 55) return SPECIAL_PRISM;
    if (roll < 67) return SPECIAL_DIAGONAL;
    if (roll < 79) return SPECIAL_DRILL;
    if (roll < 91) return SPECIAL_PULSE;
    return SPECIAL_THUNDER;
}

static int choose_rocket_column(void) {
    int occupied[COLS];
    int count = 0;
    for (int x = 0; x < COLS; ++x) {
        for (int y = 0; y < ROWS; ++y) {
            if (board[y][x]) { occupied[count++] = x; break; }
        }
    }
    return count ? occupied[rand() % count] : rand() % COLS;
}

static void advance_next_piece(void) {
    next_piece = draw_from_bag();
    roll_special(&next_special_index, &next_special_type);
}

static uint64_t monotonic_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ull + (uint64_t)ts.tv_nsec;
}

static int draw_from_bag(void) {
    if (bag_pos >= PIECES) {
        for (int i = 0; i < PIECES; ++i) bag[i] = i;
        for (int i = PIECES - 1; i > 0; --i) {
            int j = rand() % (i + 1);
            int tmp = bag[i]; bag[i] = bag[j]; bag[j] = tmp;
        }
        bag_pos = 0;
    }
    return bag[bag_pos++];
}

static void roll_special(int *index, int *type) {
    if (overdrive_time > 0.0 || rand() % 100 < 24) {
        *index = rand() % 4;
        *type = random_special_type();
    } else {
        *index = -1;
        *type = SPECIAL_NONE;
    }
}

static bool can_place(int type, int rotation, int px, int py) {
    for (int i = 0; i < 4; ++i) {
        int x = px + shapes[type][rotation][i].x;
        int y = py + shapes[type][rotation][i].y;
        if (x < 0 || x >= COLS || y >= ROWS) return false;
        if (y >= 0 && board[y][x] != 0) return false;
    }
    return true;
}

static void spawn_piece(void) {
    waiting_for_settle = false;
    settle_accumulator = 0.0;
    if (meteor_shower_remaining > 0) {
        rocket.active = true;
        rocket.mode = 1;
        rocket.column = choose_rocket_column();
        rocket.y = -1.2;
        --meteor_shower_remaining;
        advance_next_piece();
        return;
    }
    if (rand() % 200 == 0) {
        meteor_shower_remaining = 2;
        rocket.active = true;
        rocket.mode = 1;
        rocket.column = choose_rocket_column();
        rocket.y = -1.2;
        advance_next_piece();
        return;
    }
    if (rand() % 100 == 0) {
        rocket.active = true;
        rocket.mode = 0;
        rocket.column = choose_rocket_column();
        rocket.y = -1.2;
        advance_next_piece();
        return;
    }
    if (minecraft_time <= 0.0 && rand() % 100 == 0)
        start_minecraft_event();
    if (overdrive_time <= 0.0 && rand() % 150 == 0) {
        overdrive_time = 10.0;
        overdrive_banner_timer = 2.2;
        flash_time = 0.20;
        flash_kind = SPECIAL_THUNDER;
        shake_time = 0.24;
        if (shake_strength < 5.5) shake_strength = 5.5;
        if (next_special_type == SPECIAL_NONE) {
            next_special_index = rand() % 4;
            next_special_type = random_special_type();
        }
    }
    if (rand() % 250 == 0) {
        trigger_garbage_surge();
        if (game_over) return;
    }
    rocket.active = false;
    current.type = next_piece;
    current.rotation = 0;
    current.x = 3;
    current.y = -1;
    current.special_index = next_special_index;
    current.special_type = next_special_type;
    advance_next_piece();
    if (!can_place(current.type, current.rotation, current.x, current.y)) {
        if (!activate_rescue_shield() ||
            !can_place(current.type, current.rotation, current.x, current.y)) {
            game_over = true;
            if (score > high_score) high_score = score;
        }
    }
}

static void reset_game(void) {
    save_high_score();
    memset(board, 0, sizeof(board));
    memset(board_special, 0, sizeof(board_special));
    memset(effect_kind, 0, sizeof(effect_kind));
    memset(effect_variant, 0, sizeof(effect_variant));
    memset(effect_timer, 0, sizeof(effect_timer));
    memset(fall_offset, 0, sizeof(fall_offset));
    memset(particles, 0, sizeof(particles));
    memset(shockwaves, 0, sizeof(shockwaves));
    memset(score_popups, 0, sizeof(score_popups));
    memset(pending_clear_rows, 0, sizeof(pending_clear_rows));
    score = 0;
    lines = 0;
    level = 1;
    paused = false;
    game_over = false;
    gravity_accumulator = 0.0;
    elapsed_time = 0.0;
    visual_time = 0.0;
    shake_time = 0.0;
    shake_strength = 0.0;
    flash_time = 0.0;
    flash_kind = SPECIAL_NONE;
    settle_accumulator = 0.0;
    waiting_for_settle = false;
    last_clear_started_physics = false;
    normal_clear_active = false;
    normal_clear_timer = 0.0;
    pending_clear_count = 0;
    normal_clear_variant = 0;
    meteor_shower_remaining = 0;
    cascade_chain = 0;
    chain_display_timer = 0.0;
    focus_charge = 0.0;
    focus_time = 0.0;
    danger_event_timer = 0.0;
    danger_flash_time = 0.0;
    board_rise_offset = 0.0;
    perfect_clear_timer = 0.0;
    perfect_clear_candidate = false;
    overdrive_time = 0.0;
    overdrive_banner_timer = 0.0;
    flow_streak = 0;
    flow_display_timer = 0.0;
    rescue_shield = false;
    next_shield_lines = 10;
    shield_banner_timer = 0.0;
    minecraft_time = 0.0;
    minecraft_banner_timer = 0.0;
    minecraft_flash_time = 0.0;
    score_popup_cursor = 0;
    particle_cursor = 0;
    wave_cursor = 0;
    rocket.active = false;
    bag_pos = PIECES;
    next_piece = draw_from_bag();
    roll_special(&next_special_index, &next_special_type);
    spawn_piece();
}

static int clear_full_lines(void) {
    typedef struct { int x, y, special, color; } Cell;
    bool clear_row[ROWS] = {false};
    bool activated[ROWS][COLS] = {{false}};
    bool queued[ROWS][COLS] = {{false}};
    Cell queue[ROWS * COLS];
    int queue_begin = 0, queue_end = 0;
    int cleared = 0;
    last_clear_started_physics = false;
    for (int y = 0; y < ROWS; ++y) {
        bool full = true;
        for (int x = 0; x < COLS; ++x) {
            if (board[y][x] == 0) { full = false; break; }
        }
        if (!full) continue;
        clear_row[y] = true;
        ++cleared;
        for (int x = 0; x < COLS; ++x)
            if (board_special[y][x] != SPECIAL_NONE) {
                queue[queue_end++] = (Cell){x, y, board_special[y][x],
                                           board[y][x]};
                queued[y][x] = true;
            }
    }

    last_clear_started_physics = queue_end > 0;
    bool use_individual_physics = waiting_for_settle ||
                                  last_clear_started_physics;

    /* Specials hit by another special join the same chain reaction. */
    while (queue_begin < queue_end) {
        Cell source = queue[queue_begin++];
        if (activated[source.y][source.x]) continue;
        int special = source.special;
        if (special == SPECIAL_NONE) continue;
        activated[source.y][source.x] = true;
        int variant = rand() % 3;
        start_special_impact(source.x, source.y, special, variant);

        if (special == SPECIAL_BOMB) {
            for (int y = source.y - 3; y <= source.y + 3; ++y) {
                for (int x = source.x - 3; x <= source.x + 3; ++x) {
                    if (x < 0 || x >= COLS || y < 0 || y >= ROWS) continue;
                    effect_kind[y][x] = SPECIAL_BOMB;
                    effect_variant[y][x] = (unsigned char)variant;
                    effect_timer[y][x] = 0.36;
                    if (board[y][x] && board_special[y][x] != SPECIAL_NONE &&
                        !queued[y][x] && queue_end < ROWS * COLS) {
                        queue[queue_end++] = (Cell){x, y, board_special[y][x],
                                                   board[y][x]};
                        queued[y][x] = true;
                    }
                    if (board[y][x]) {
                        spawn_fragments(x, y, board[y][x], special,
                                        source.x, source.y);
                        int points = award_points(12 * level);
                        add_focus_charge(2.0);
                        spawn_cell_score(x, y, points, (Color){1.0, 0.55, 0.16});
                    }
                    board[y][x] = 0;
                    board_special[y][x] = SPECIAL_NONE;
                    fall_offset[y][x] = 0.0;
                }
            }
        } else if (special == SPECIAL_LASER) {
            for (int y = source.y; y >= 0; --y) {
                effect_kind[y][source.x] = SPECIAL_LASER;
                effect_variant[y][source.x] = (unsigned char)variant;
                effect_timer[y][source.x] = 0.36;
                if (board[y][source.x] &&
                    board_special[y][source.x] != SPECIAL_NONE &&
                    !queued[y][source.x] && queue_end < ROWS * COLS) {
                    queue[queue_end++] = (Cell){source.x, y,
                                               board_special[y][source.x],
                                               board[y][source.x]};
                    queued[y][source.x] = true;
                }
                if (board[y][source.x]) {
                    spawn_fragments(source.x, y, board[y][source.x], special,
                                    source.x, source.y);
                    int points = award_points(12 * level);
                    add_focus_charge(2.0);
                    spawn_cell_score(source.x, y, points,
                                     (Color){0.30, 0.95, 1.0});
                }
                board[y][source.x] = 0;
                board_special[y][source.x] = SPECIAL_NONE;
                fall_offset[y][source.x] = 0.0;
            }
        } else if (special == SPECIAL_CROSS) {
            for (int y = 0; y < ROWS; ++y) {
                for (int x = 0; x < COLS; ++x) {
                    if (x != source.x && y != source.y) continue;
                    effect_kind[y][x] = SPECIAL_CROSS;
                    effect_variant[y][x] = (unsigned char)variant;
                    effect_timer[y][x] = 0.42;
                    if (board[y][x] && board_special[y][x] != SPECIAL_NONE &&
                        !queued[y][x] && queue_end < ROWS * COLS) {
                        queue[queue_end++] = (Cell){x, y, board_special[y][x],
                                                   board[y][x]};
                        queued[y][x] = true;
                    }
                    if (board[y][x]) {
                        spawn_fragments(x, y, board[y][x], special,
                                        source.x, source.y);
                        int points = award_points(14 * level);
                        add_focus_charge(2.0);
                        spawn_cell_score(x, y, points,
                                         (Color){0.78, 0.42, 1.0});
                    }
                    board[y][x] = 0;
                    board_special[y][x] = SPECIAL_NONE;
                    fall_offset[y][x] = 0.0;
                }
            }
        } else if (special == SPECIAL_PRISM) {
            int target_color = source.color;
            for (int y = 0; y < ROWS; ++y) {
                for (int x = 0; x < COLS; ++x) {
                    if (board[y][x] != target_color) continue;
                    effect_kind[y][x] = SPECIAL_PRISM;
                    effect_variant[y][x] = (unsigned char)variant;
                    effect_timer[y][x] = 0.50;
                    if (board_special[y][x] != SPECIAL_NONE &&
                        !queued[y][x] && queue_end < ROWS * COLS) {
                        queue[queue_end++] = (Cell){x, y, board_special[y][x],
                                                   board[y][x]};
                        queued[y][x] = true;
                    }
                    spawn_fragments(x, y, board[y][x], special,
                                    source.x, source.y);
                    int points = award_points(8 * level);
                    add_focus_charge(1.0);
                    spawn_cell_score(x, y, points,
                                     piece_colors[target_color]);
                    board[y][x] = 0;
                    board_special[y][x] = SPECIAL_NONE;
                    fall_offset[y][x] = 0.0;
                }
            }
        } else if (special == SPECIAL_DIAGONAL) {
            for (int y = 0; y < ROWS; ++y) {
                for (int x = 0; x < COLS; ++x) {
                    int dx = x - source.x; if (dx < 0) dx = -dx;
                    int dy = y - source.y; if (dy < 0) dy = -dy;
                    if (dx != dy) continue;
                    effect_kind[y][x] = SPECIAL_DIAGONAL;
                    effect_variant[y][x] = (unsigned char)variant;
                    effect_timer[y][x] = 0.44;
                    if (board[y][x] && board_special[y][x] != SPECIAL_NONE &&
                        !queued[y][x] && queue_end < ROWS * COLS) {
                        queue[queue_end++] = (Cell){x, y, board_special[y][x],
                                                   board[y][x]};
                        queued[y][x] = true;
                    }
                    if (board[y][x]) {
                        spawn_fragments(x, y, board[y][x], special,
                                        source.x, source.y);
                        int points = award_points(11 * level);
                        add_focus_charge(1.5);
                        spawn_cell_score(x, y, points,
                                         (Color){0.35, 1.0, 0.58});
                    }
                    board[y][x] = 0;
                    board_special[y][x] = SPECIAL_NONE;
                    fall_offset[y][x] = 0.0;
                }
            }
        } else if (special == SPECIAL_DRILL) {
            for (int y = source.y; y < ROWS; ++y) {
                for (int x = source.x - 1; x <= source.x + 1; ++x) {
                    if (x < 0 || x >= COLS) continue;
                    effect_kind[y][x] = SPECIAL_DRILL;
                    effect_variant[y][x] = (unsigned char)variant;
                    effect_timer[y][x] = 0.46;
                    if (board[y][x] && board_special[y][x] != SPECIAL_NONE &&
                        !queued[y][x] && queue_end < ROWS * COLS) {
                        queue[queue_end++] = (Cell){x, y, board_special[y][x],
                                                   board[y][x]};
                        queued[y][x] = true;
                    }
                    if (board[y][x]) {
                        spawn_fragments(x, y, board[y][x], special,
                                        source.x, source.y);
                        int points = award_points(10 * level);
                        add_focus_charge(1.5);
                        spawn_cell_score(x, y, points,
                                         (Color){1.0, 0.66, 0.18});
                    }
                    board[y][x] = 0;
                    board_special[y][x] = SPECIAL_NONE;
                    fall_offset[y][x] = 0.0;
                }
            }
        } else if (special == SPECIAL_PULSE) {
            for (int y = source.y - 2; y <= source.y + 2; ++y) {
                for (int x = source.x - 2; x <= source.x + 2; ++x) {
                    if (x < 0 || x >= COLS || y < 0 || y >= ROWS) continue;
                    int dx = x - source.x; if (dx < 0) dx = -dx;
                    int dy = y - source.y; if (dy < 0) dy = -dy;
                    if ((dx > dy ? dx : dy) != 2) continue;
                    effect_kind[y][x] = SPECIAL_PULSE;
                    effect_variant[y][x] = (unsigned char)variant;
                    effect_timer[y][x] = 0.48;
                    if (board[y][x] && board_special[y][x] != SPECIAL_NONE &&
                        !queued[y][x] && queue_end < ROWS * COLS) {
                        queue[queue_end++] = (Cell){x, y, board_special[y][x],
                                                   board[y][x]};
                        queued[y][x] = true;
                    }
                    if (board[y][x]) {
                        spawn_fragments(x, y, board[y][x], special,
                                        source.x, source.y);
                        int points = award_points(9 * level);
                        add_focus_charge(1.25);
                        spawn_cell_score(x, y, points,
                                         (Color){1.0, 0.88, 0.22});
                    }
                    board[y][x] = 0;
                    board_special[y][x] = SPECIAL_NONE;
                    fall_offset[y][x] = 0.0;
                }
            }
        } else if (special == SPECIAL_THUNDER) {
            for (int x = 0; x < COLS; ++x) {
                int y = 0;
                while (y < ROWS && board[y][x] == 0) ++y;
                if (y >= ROWS) continue;
                effect_kind[y][x] = SPECIAL_THUNDER;
                effect_variant[y][x] = (unsigned char)variant;
                effect_timer[y][x] = 0.42;
                if (board_special[y][x] != SPECIAL_NONE && !queued[y][x] &&
                    queue_end < ROWS * COLS) {
                    queue[queue_end++] = (Cell){x, y, board_special[y][x],
                                               board[y][x]};
                    queued[y][x] = true;
                }
                spawn_fragments(x, y, board[y][x], special,
                                source.x, source.y);
                int points = award_points(11 * level);
                add_focus_charge(1.5);
                spawn_cell_score(x, y, points,
                                 (Color){0.72, 0.92, 1.0});
                board[y][x] = 0;
                board_special[y][x] = SPECIAL_NONE;
                fall_offset[y][x] = 0.0;
            }
        }
    }

    if (cleared == 0) return 0;

    if (use_individual_physics) {
        for (int y = 0; y < ROWS; ++y) {
            if (!clear_row[y]) continue;
            memset(board[y], 0, sizeof(board[y]));
            memset(board_special[y], 0, sizeof(board_special[y]));
            memset(fall_offset[y], 0, sizeof(fall_offset[y]));
        }
    } else {
        normal_clear_active = true;
        normal_clear_timer = 0.34;
        pending_clear_count = cleared;
        normal_clear_variant = rand() % 4;
        memcpy(pending_clear_rows, clear_row, sizeof(pending_clear_rows));
        for (int y = 0; y < ROWS; ++y) {
            if (!clear_row[y]) continue;
            for (int x = 0; x < COLS; ++x) {
                if (board[y][x]) spawn_line_fragments(x, y, board[y][x]);
            }
        }
    }
    return cleared;
}

static int resolve_completed_lines(void) {
    int cleared = clear_full_lines();
    if (cleared == 0) return 0;
    perfect_clear_candidate = true;
    static const int rewards[5] = {0, 100, 300, 500, 800};
    int reward_index = cleared > 4 ? 4 : cleared;
    int line_points = rewards[reward_index] * level;
    if (waiting_for_settle) {
        ++cascade_chain;
        line_points *= cascade_chain + 1;
        chain_display_timer = 1.15;
    }
    line_points = award_points(line_points);
    add_focus_charge(cleared * 24.0);
    lines += cleared;
    while (lines >= next_shield_lines) {
        rescue_shield = true;
        shield_banner_timer = 2.0;
        next_shield_lines += 10;
    }
    level = 1 + lines / 10 + (int)(elapsed_time / 35.0);
    if (normal_clear_active) {
        int sum_y = 0;
        for (int y = 0; y < ROWS; ++y)
            if (pending_clear_rows[y]) sum_y += y;
        int row = pending_clear_count ? sum_y / pending_clear_count : ROWS / 2;
        spawn_score_popup(BOARD_X + COLS * CELL / 2.0,
                          BOARD_Y + (ROWS - row - 0.5) * CELL,
                          line_points,
                          (Color){1.0, 0.95, 0.60});
    }
    return cleared;
}

static bool has_floating_blocks(void) {
    for (int y = 0; y < ROWS - 1; ++y)
        for (int x = 0; x < COLS; ++x)
            if (board[y][x] && board[y + 1][x] == 0) return true;
    return false;
}

static bool apply_block_gravity_step(void) {
    bool moved = false;
    for (int y = ROWS - 2; y >= 0; --y) {
        for (int x = 0; x < COLS; ++x) {
            if (!board[y][x] || board[y + 1][x]) continue;
            board[y + 1][x] = board[y][x];
            board_special[y + 1][x] = board_special[y][x];
            fall_offset[y + 1][x] = fall_offset[y][x] + CELL;
            board[y][x] = 0;
            board_special[y][x] = SPECIAL_NONE;
            fall_offset[y][x] = 0.0;
            moved = true;
        }
    }
    return moved;
}

static void begin_settling_or_spawn(void) {
    if (has_floating_blocks()) {
        waiting_for_settle = true;
        settle_accumulator = 0.0;
        cascade_chain = 0;
    } else {
        check_perfect_clear();
        spawn_piece();
    }
}

static void complete_normal_line_clear(void) {
    int write = ROWS - 1;
    for (int read = ROWS - 1; read >= 0; --read) {
        if (pending_clear_rows[read]) continue;
        if (write != read) {
            memcpy(board[write], board[read], sizeof(board[write]));
            memcpy(board_special[write], board_special[read],
                   sizeof(board_special[write]));
        }
        memset(fall_offset[write], 0, sizeof(fall_offset[write]));
        --write;
    }
    while (write >= 0) {
        memset(board[write], 0, sizeof(board[write]));
        memset(board_special[write], 0, sizeof(board_special[write]));
        memset(fall_offset[write], 0, sizeof(fall_offset[write]));
        --write;
    }
    memset(pending_clear_rows, 0, sizeof(pending_clear_rows));
    pending_clear_count = 0;
    normal_clear_timer = 0.0;
    normal_clear_active = false;
    check_perfect_clear();
    spawn_piece();
}

static void spawn_rocket_trail(void) {
    double center_x = BOARD_X + (rocket.column + 0.5) * CELL;
    double center_y = BOARD_Y + (ROWS - rocket.y - 0.5) * CELL;
    for (int i = 0; i < 5; ++i) {
        Particle *p = &particles[particle_cursor++ % MAX_PARTICLES];
        p->active = true;
        p->x = center_x + (random_unit() - 0.5) * 8.0;
        p->y = center_y + 15.0 + random_unit() * 10.0;
        p->vx = (random_unit() - 0.5) * 45.0;
        p->vy = 45.0 + random_unit() * 80.0;
        p->max_life = 0.20 + random_unit() * 0.18;
        p->life = p->max_life;
        p->size = 3.0 + random_unit() * 4.0;
        p->color = rocket.mode
            ? (i == 0 ? (Color){0.42, 0.95, 1.0} : (Color){0.68, 0.30, 1.0})
            : (i == 0 ? (Color){1.0, 0.95, 0.35} : (Color){1.0, 0.28, 0.06});
    }
}

static void explode_rocket(int center_x, int center_y) {
    bool destroyed_any = false;
    int impact = rocket.mode ? SPECIAL_METEOR : SPECIAL_ROCKET;
    int radius = rocket.mode ? 2 : 3;
    int variant = rand() % 3;
    start_special_impact(center_x, center_y, impact, variant);
    for (int y = center_y - radius; y <= center_y + radius; ++y) {
        for (int x = center_x - radius; x <= center_x + radius; ++x) {
            if (x < 0 || x >= COLS || y < 0 || y >= ROWS) continue;
            effect_kind[y][x] = (unsigned char)impact;
            effect_variant[y][x] = (unsigned char)variant;
            effect_timer[y][x] = rocket.mode ? 0.46 : 0.54;
            if (board[y][x]) {
                spawn_fragments(x, y, board[y][x], impact,
                                center_x, center_y);
                int points = award_points((rocket.mode ? 10 : 12) * level);
                add_focus_charge(1.5);
                spawn_cell_score(x, y, points, rocket.mode
                    ? (Color){0.72, 0.45, 1.0} : (Color){1.0, 0.62, 0.18});
                board[y][x] = 0;
                board_special[y][x] = SPECIAL_NONE;
                fall_offset[y][x] = 0.0;
                destroyed_any = true;
            }
        }
    }
    if (destroyed_any) perfect_clear_candidate = true;
    rocket.active = false;
    begin_settling_or_spawn();
}

static void update_rocket(double dt) {
    spawn_rocket_trail();
    double previous_y = rocket.y;
    rocket.y += 12.0 * dt;
    int first_row = previous_y < 0.0 ? 0 : (int)previous_y;
    int last_row = (int)rocket.y;
    if (last_row >= ROWS) last_row = ROWS - 1;
    for (int y = first_row; y <= last_row; ++y) {
        if (board[y][rocket.column]) {
            explode_rocket(rocket.column, y);
            return;
        }
    }
    if (rocket.y >= ROWS)
        explode_rocket(rocket.column, ROWS - 1);
}

static void steer_rocket(int direction) {
    int column = rocket.column + direction;
    if (column < 0 || column >= COLS) return;
    rocket.column = column;

    if (rocket.y >= 0.0 && rocket.y < ROWS) {
        int row = (int)rocket.y;
        if (board[row][rocket.column])
            explode_rocket(rocket.column, row);
    }
}

static void lock_piece(void) {
    bool above_top = false;
    for (int i = 0; i < 4; ++i) {
        int x = current.x + shapes[current.type][current.rotation][i].x;
        int y = current.y + shapes[current.type][current.rotation][i].y;
        if (y < 0) above_top = true;
        else {
            board[y][x] = current.type + 1;
            board_special[y][x] = (i == current.special_index)
                ? current.special_type : SPECIAL_NONE;
        }
    }
    if (above_top) {
        flow_streak = 0;
        if (activate_rescue_shield()) {
            spawn_piece();
        } else {
            game_over = true;
            if (score > high_score) high_score = score;
        }
        return;
    }
    int cleared = resolve_completed_lines();
    if (cleared > 0) {
        ++flow_streak;
        flow_display_timer = 1.5;
        if (flow_streak >= 2) {
            int bonus = award_points((flow_streak - 1) * 75 * level);
            spawn_score_popup(BOARD_X + COLS * CELL / 2.0,
                              BOARD_Y + ROWS * CELL - 105.0,
                              bonus, (Color){0.42, 1.0, 0.82});
        }
    } else {
        flow_streak = 0;
    }
    if (normal_clear_active) return;
    if (last_clear_started_physics) begin_settling_or_spawn();
    else spawn_piece();
}

static bool move_piece(int dx, int dy) {
    if (!can_place(current.type, current.rotation, current.x + dx, current.y + dy))
        return false;
    current.x += dx;
    current.y += dy;
    return true;
}

static void rotate_piece(int direction) {
    int rotation = (current.rotation + direction + 4) % 4;
    static const Block kicks[] = {{0,0},{-1,0},{1,0},{-2,0},{2,0},{0,-1},{-1,-1},{1,-1}};
    for (size_t i = 0; i < sizeof(kicks) / sizeof(kicks[0]); ++i) {
        int x = current.x + kicks[i].x;
        int y = current.y + kicks[i].y;
        if (can_place(current.type, rotation, x, y)) {
            current.rotation = rotation;
            current.x = x;
            current.y = y;
            return;
        }
    }
}

static double gravity_delay(void) {
    double delay = 0.84 - (double)(level - 1) * 0.055;
    if (delay < 0.095) delay = 0.095;
    if (focus_time > 0.0) delay *= 1.75;
    if (overdrive_time > 0.0) delay *= 0.72;
    return delay;
}

static void update_settling(double dt) {
    const double step_time = 0.065;
    double fall_speed = CELL / step_time;
    for (int y = 0; y < ROWS; ++y) {
        for (int x = 0; x < COLS; ++x) {
            if (fall_offset[y][x] > 0.0) {
                fall_offset[y][x] -= fall_speed * dt;
                if (fall_offset[y][x] < 0.0) fall_offset[y][x] = 0.0;
            }
        }
    }

    settle_accumulator += dt;
    while (settle_accumulator >= step_time && waiting_for_settle) {
        settle_accumulator -= step_time;
        resolve_completed_lines();
        if (!apply_block_gravity_step()) {
            waiting_for_settle = false;
            memset(fall_offset, 0, sizeof(fall_offset));
            check_perfect_clear();
            spawn_piece();
        }
    }
}

static void update_game(double dt) {
    visual_time += dt;
    if (danger_event_timer > 0.0) {
        danger_event_timer -= dt;
        if (danger_event_timer < 0.0) danger_event_timer = 0.0;
    }
    if (danger_flash_time > 0.0) {
        danger_flash_time -= dt;
        if (danger_flash_time < 0.0) danger_flash_time = 0.0;
    }
    if (perfect_clear_timer > 0.0) {
        perfect_clear_timer -= dt;
        if (perfect_clear_timer < 0.0) perfect_clear_timer = 0.0;
    }
    if (overdrive_banner_timer > 0.0) {
        overdrive_banner_timer -= dt;
        if (overdrive_banner_timer < 0.0) overdrive_banner_timer = 0.0;
    }
    if (flow_display_timer > 0.0) {
        flow_display_timer -= dt;
        if (flow_display_timer < 0.0) flow_display_timer = 0.0;
    }
    if (shield_banner_timer > 0.0) {
        shield_banner_timer -= dt;
        if (shield_banner_timer < 0.0) shield_banner_timer = 0.0;
    }
    if (minecraft_banner_timer > 0.0) {
        minecraft_banner_timer -= dt;
        if (minecraft_banner_timer < 0.0) minecraft_banner_timer = 0.0;
    }
    if (minecraft_flash_time > 0.0) {
        minecraft_flash_time -= dt;
        if (minecraft_flash_time < 0.0) minecraft_flash_time = 0.0;
    }
    if (board_rise_offset < 0.0) {
        board_rise_offset += (CELL / 0.34) * dt;
        if (board_rise_offset > 0.0) board_rise_offset = 0.0;
    }
    if (chain_display_timer > 0.0) {
        chain_display_timer -= dt;
        if (chain_display_timer < 0.0) chain_display_timer = 0.0;
    }
    if (shake_time > 0.0) {
        shake_time -= dt;
        if (shake_time <= 0.0) {
            shake_time = 0.0;
            shake_strength = 0.0;
        }
    }
    if (flash_time > 0.0) {
        flash_time -= dt;
        if (flash_time < 0.0) flash_time = 0.0;
    }
    for (int i = 0; i < MAX_PARTICLES; ++i) {
        Particle *p = &particles[i];
        if (!p->active) continue;
        p->life -= dt;
        if (p->life <= 0.0) { p->active = false; continue; }
        p->vy -= 310.0 * dt;
        p->x += p->vx * dt;
        p->y += p->vy * dt;
        p->vx *= 1.0 - 0.8 * dt;
    }
    for (int i = 0; i < MAX_WAVES; ++i) {
        if (!shockwaves[i].active) continue;
        shockwaves[i].life -= dt;
        if (shockwaves[i].life <= 0.0) shockwaves[i].active = false;
    }
    for (int i = 0; i < MAX_SCORE_POPUPS; ++i) {
        ScorePopup *popup = &score_popups[i];
        if (!popup->active) continue;
        popup->life -= dt;
        if (popup->life <= 0.0) { popup->active = false; continue; }
        popup->y += popup->vy * dt;
        popup->vy *= 1.0 - 1.4 * dt;
    }
    for (int y = 0; y < ROWS; ++y) {
        for (int x = 0; x < COLS; ++x) {
            if (effect_timer[y][x] > 0.0) {
                effect_timer[y][x] -= dt;
                if (effect_timer[y][x] <= 0.0) {
                    effect_timer[y][x] = 0.0;
                    effect_kind[y][x] = SPECIAL_NONE;
                    effect_variant[y][x] = 0;
                }
            }
        }
    }
    if (game_over) {
        save_high_score();
        return;
    }
    if (paused) return;
    if (minecraft_time > 0.0) {
        minecraft_time -= dt;
        if (minecraft_time < 0.0) minecraft_time = 0.0;
    }
    if (overdrive_time > 0.0) {
        overdrive_time -= dt;
        if (overdrive_time < 0.0) overdrive_time = 0.0;
    }
    if (focus_time > 0.0) {
        focus_time -= dt;
        if (focus_time < 0.0) focus_time = 0.0;
    }
    elapsed_time += dt;
    level = 1 + lines / 10 + (int)(elapsed_time / 35.0);
    if (normal_clear_active) {
        normal_clear_timer -= dt;
        if (normal_clear_timer <= 0.0) complete_normal_line_clear();
        return;
    }
    if (rocket.active) {
        update_rocket(dt);
        return;
    }
    if (waiting_for_settle) {
        update_settling(dt);
        return;
    }
    gravity_accumulator += dt;
    double delay = gravity_delay();
    while (gravity_accumulator >= delay) {
        gravity_accumulator -= delay;
        if (!move_piece(0, 1)) { lock_piece(); break; }
    }
}

static void handle_key(unsigned short key) {
    if (key == 53 || key == 12) { running = false; return; } /* Esc, Q */
    if (key == 15) { reset_game(); return; }                 /* R */
    if (key == 35 && !game_over) { paused = !paused; return; } /* P */
    if (paused || game_over) return;
    if (key == 14 && focus_time <= 0.0 && focus_charge >= 100.0 &&
        !rocket.active && !waiting_for_settle && !normal_clear_active) { /* E */
        focus_charge = 0.0;
        focus_time = 8.0;
        chain_display_timer = 1.15;
        return;
    }
    if (normal_clear_active) return;
    if (rocket.active) {
        switch (key) {
            case 0: steer_rocket(-1); break;                 /* A */
            case 2: steer_rocket(1); break;                  /* D */
            case 1: update_rocket(0.10); break;              /* S */
            default: break;
        }
        return;
    }
    if (waiting_for_settle) return;

    switch (key) {
        case 0: move_piece(-1, 0); break;                    /* A */
        case 2: move_piece(1, 0); break;                     /* D */
        case 1:                                              /* S */
            if (move_piece(0, 1)) award_points(1); else lock_piece();
            gravity_accumulator = 0.0;
            break;
        case 13: case 7: rotate_piece(1); break;             /* W, X */
        case 6: rotate_piece(-1); break;                     /* Z */
        case 49: {                                           /* Space */
            int distance = 0;
            while (move_piece(0, 1)) ++distance;
            award_points(distance * 2);
            lock_piece();
            gravity_accumulator = 0.0;
            break;
        }
        default: break;
    }
    if (score > high_score) high_score = score;
}

static void set_fill(CGContextRef ctx, Color c, double alpha) {
    CGContextSetRGBFillColor(ctx, c.r, c.g, c.b, alpha);
}

static void fill_rect(CGContextRef ctx, double x, double y, double w, double h,
                      Color color, double alpha) {
    set_fill(ctx, color, alpha);
    CGContextFillRect(ctx, CGRectMake(x, y, w, h));
}

static const uint8_t font5x7[36][7] = {
    {14,17,17,31,17,17,17},{30,17,17,30,17,17,30},{14,17,16,16,16,17,14},
    {30,17,17,17,17,17,30},{31,16,16,30,16,16,31},{31,16,16,30,16,16,16},
    {14,17,16,23,17,17,15},{17,17,17,31,17,17,17},{31,4,4,4,4,4,31},
    {7,2,2,2,18,18,12},{17,18,20,24,20,18,17},{16,16,16,16,16,16,31},
    {17,27,21,21,17,17,17},{17,25,21,19,17,17,17},{14,17,17,17,17,17,14},
    {30,17,17,30,16,16,16},{14,17,17,17,21,18,13},{30,17,17,30,20,18,17},
    {15,16,16,14,1,1,30},{31,4,4,4,4,4,4},{17,17,17,17,17,17,14},
    {17,17,17,17,17,10,4},{17,17,17,21,21,21,10},{17,17,10,4,10,17,17},
    {17,17,10,4,4,4,4},{31,1,2,4,8,16,31},
    {14,17,19,21,25,17,14},{4,12,4,4,4,4,14},{14,17,1,2,4,8,31},
    {30,1,1,14,1,1,30},{2,6,10,18,31,2,2},{31,16,30,1,1,17,14},
    {6,8,16,30,17,17,14},{31,1,2,4,8,8,8},{14,17,17,14,17,17,14},
    {14,17,17,15,1,2,12}
};

static const uint8_t *glyph_for(char c) {
    if (c >= 'A' && c <= 'Z') return font5x7[c - 'A'];
    if (c >= '0' && c <= '9') return font5x7[26 + c - '0'];
    return NULL;
}

static double text_width(const char *text, int scale) {
    size_t len = strlen(text);
    return len ? (double)(len * 6 - 1) * scale : 0.0;
}

static void draw_text_alpha(CGContextRef ctx, const char *text, double x, double y,
                            int scale, Color color, double alpha) {
    set_fill(ctx, color, alpha);
    for (size_t i = 0; text[i]; ++i) {
        const uint8_t *glyph = glyph_for(text[i]);
        if (glyph) {
            for (int row = 0; row < 7; ++row)
                for (int col = 0; col < 5; ++col)
                    if (glyph[row] & (1u << (4 - col)))
                        CGContextFillRect(ctx, CGRectMake(x + col * scale,
                            y + (6 - row) * scale, scale, scale));
        }
        x += 6 * scale;
    }
}

static void draw_text(CGContextRef ctx, const char *text, double x, double y,
                      int scale, Color color) {
    draw_text_alpha(ctx, text, x, y, scale, color, 1.0);
}

static void draw_centered(CGContextRef ctx, const char *text, double center_x,
                          double y, int scale, Color color) {
    draw_text(ctx, text, center_x - text_width(text, scale) / 2.0, y, scale, color);
}

static void draw_special_marker(CGContextRef ctx, double x, double y, int size,
                                int special, double alpha) {
    if (special == SPECIAL_NONE) return;
    Color dark = {0.025, 0.035, 0.055};
    Color glow = {1.0, 0.35, 0.82};
    if (special == SPECIAL_BOMB) glow = (Color){1.0, 0.24, 0.12};
    else if (special == SPECIAL_LASER) glow = (Color){0.20, 0.95, 1.0};
    else if (special == SPECIAL_CROSS) glow = (Color){0.78, 0.38, 1.0};
    else if (special == SPECIAL_DIAGONAL) glow = (Color){0.32, 1.0, 0.55};
    else if (special == SPECIAL_DRILL) glow = (Color){1.0, 0.62, 0.15};
    else if (special == SPECIAL_PULSE) glow = (Color){1.0, 0.88, 0.18};
    else if (special == SPECIAL_THUNDER) glow = (Color){0.62, 0.88, 1.0};
    double inset = size >= 28 ? 6.0 : 5.0;
    CGRect badge = CGRectMake(x + inset, y + inset,
                              size - inset * 2.0, size - inset * 2.0);
    fill_rect(ctx, badge.origin.x - 2, badge.origin.y - 2,
              badge.size.width + 4, badge.size.height + 4, glow, 0.58 * alpha);
    double marker_pulse = ((uint32_t)(visual_time * 10.0 + x + y) % 2u)
        ? 0.34 : 0.18;
    fill_rect(ctx, badge.origin.x - 4, badge.origin.y - 4,
              badge.size.width + 8, badge.size.height + 8,
              glow, marker_pulse * alpha);
    fill_rect(ctx, badge.origin.x, badge.origin.y,
              badge.size.width, badge.size.height, dark, 0.94 * alpha);
    CGContextSetRGBStrokeColor(ctx, glow.r, glow.g, glow.b, alpha);
    CGContextSetLineWidth(ctx, 2.0);
    CGContextStrokeRect(ctx, badge);

    if (special == SPECIAL_BOMB) {
        CGContextSetRGBFillColor(ctx, glow.r, glow.g, glow.b, alpha);
        CGContextFillEllipseInRect(ctx, CGRectInset(badge, 4.0, 4.0));
        CGContextSetRGBStrokeColor(ctx, 1.0, 0.85, 0.25, alpha);
        CGContextSetLineWidth(ctx, 2.0);
        CGContextMoveToPoint(ctx, CGRectGetMidX(badge) + 2,
                             CGRectGetMaxY(badge) - 4);
        CGContextAddLineToPoint(ctx, CGRectGetMaxX(badge) + 1,
                                CGRectGetMaxY(badge) + 2);
        CGContextStrokePath(ctx);
    } else if (special == SPECIAL_LASER) {
        double mid = CGRectGetMidX(badge);
        fill_rect(ctx, mid - 2, CGRectGetMinY(badge) + 2, 4,
                  badge.size.height - 4, glow, alpha);
        fill_rect(ctx, mid - 6, CGRectGetMaxY(badge) - 6, 12, 3,
                  glow, alpha);
    } else if (special == SPECIAL_CROSS) {
        double mid_x = CGRectGetMidX(badge);
        double mid_y = CGRectGetMidY(badge);
        fill_rect(ctx, CGRectGetMinX(badge) + 2, mid_y - 2,
                  badge.size.width - 4, 4, glow, alpha);
        fill_rect(ctx, mid_x - 2, CGRectGetMinY(badge) + 2,
                  4, badge.size.height - 4, glow, alpha);
    } else if (special == SPECIAL_PRISM) {
        CGContextBeginPath(ctx);
        CGContextMoveToPoint(ctx, CGRectGetMidX(badge), CGRectGetMaxY(badge) - 2);
        CGContextAddLineToPoint(ctx, CGRectGetMaxX(badge) - 2, CGRectGetMidY(badge));
        CGContextAddLineToPoint(ctx, CGRectGetMidX(badge), CGRectGetMinY(badge) + 2);
        CGContextAddLineToPoint(ctx, CGRectGetMinX(badge) + 2, CGRectGetMidY(badge));
        CGContextClosePath(ctx);
        CGContextSetRGBFillColor(ctx, glow.r, glow.g, glow.b, alpha);
        CGContextFillPath(ctx);
    } else if (special == SPECIAL_DIAGONAL) {
        CGContextSetRGBStrokeColor(ctx, glow.r, glow.g, glow.b, alpha);
        CGContextSetLineWidth(ctx, 3.0);
        CGContextMoveToPoint(ctx, CGRectGetMinX(badge) + 2,
                             CGRectGetMinY(badge) + 2);
        CGContextAddLineToPoint(ctx, CGRectGetMaxX(badge) - 2,
                                CGRectGetMaxY(badge) - 2);
        CGContextMoveToPoint(ctx, CGRectGetMinX(badge) + 2,
                             CGRectGetMaxY(badge) - 2);
        CGContextAddLineToPoint(ctx, CGRectGetMaxX(badge) - 2,
                                CGRectGetMinY(badge) + 2);
        CGContextStrokePath(ctx);
    } else if (special == SPECIAL_DRILL) {
        double mid = CGRectGetMidX(badge);
        fill_rect(ctx, mid - 3, CGRectGetMinY(badge) + 4, 6,
                  badge.size.height - 6, glow, alpha);
        CGContextBeginPath(ctx);
        CGContextMoveToPoint(ctx, mid - 7, CGRectGetMinY(badge) + 7);
        CGContextAddLineToPoint(ctx, mid, CGRectGetMinY(badge) + 1);
        CGContextAddLineToPoint(ctx, mid + 7, CGRectGetMinY(badge) + 7);
        CGContextClosePath(ctx);
        CGContextSetRGBFillColor(ctx, glow.r, glow.g, glow.b, alpha);
        CGContextFillPath(ctx);
    } else if (special == SPECIAL_PULSE) {
        CGContextSetRGBStrokeColor(ctx, glow.r, glow.g, glow.b, alpha);
        CGContextSetLineWidth(ctx, 3.0);
        CGContextStrokeEllipseInRect(ctx, CGRectInset(badge, 3.0, 3.0));
        CGContextSetRGBFillColor(ctx, 1.0, 0.98, 0.68, alpha);
        CGContextFillEllipseInRect(ctx, CGRectMake(CGRectGetMidX(badge) - 2,
            CGRectGetMidY(badge) - 2, 4, 4));
    } else if (special == SPECIAL_THUNDER) {
        CGContextBeginPath(ctx);
        CGContextMoveToPoint(ctx, CGRectGetMidX(badge) + 2,
                             CGRectGetMaxY(badge) - 2);
        CGContextAddLineToPoint(ctx, CGRectGetMidX(badge) - 4,
                                CGRectGetMidY(badge));
        CGContextAddLineToPoint(ctx, CGRectGetMidX(badge) + 2,
                                CGRectGetMidY(badge));
        CGContextAddLineToPoint(ctx, CGRectGetMidX(badge) - 3,
                                CGRectGetMinY(badge) + 2);
        CGContextSetRGBStrokeColor(ctx, glow.r, glow.g, glow.b, alpha);
        CGContextSetLineWidth(ctx, 3.0);
        CGContextStrokePath(ctx);
    }
}

static void draw_minecraft_tile(CGContextRef ctx, double x, double y, int size,
                                double alpha, bool grass_top, uint32_t seed) {
    Color dirt = {0.45, 0.27, 0.13};
    Color dark_dirt = {0.29, 0.16, 0.08};
    Color light_dirt = {0.62, 0.39, 0.19};
    Color grass = {0.28, 0.68, 0.16};
    Color light_grass = {0.43, 0.82, 0.22};
    fill_rect(ctx, x + 2, y + 2, size - 4, size - 4, dirt, alpha);

    double pixel = size >= 28 ? 4.0 : 3.0;
    for (int i = 0; i < 7; ++i) {
        seed = seed * 1664525u + 1013904223u;
        double px = x + 3 + (seed % (uint32_t)(size - 8));
        seed = seed * 1664525u + 1013904223u;
        double py = y + 3 + (seed % (uint32_t)(size - 8));
        Color patch = i % 3 == 0 ? light_dirt : dark_dirt;
        fill_rect(ctx, px, py, pixel, pixel, patch, 0.62 * alpha);
    }
    if (grass_top) {
        fill_rect(ctx, x + 2, y + size - 10, size - 4, 8,
                  grass, alpha);
        fill_rect(ctx, x + 3, y + size - 6, size - 6, 4,
                  light_grass, alpha);
        for (int i = 0; i < 4; ++i) {
            seed = seed * 22695477u + 1u;
            double px = x + 3 + (seed % (uint32_t)(size - 7));
            double depth = 2.0 + (seed % 5u);
            fill_rect(ctx, px, y + size - 10 - depth, pixel, depth,
                      grass, alpha);
        }
    }
    CGContextSetRGBStrokeColor(ctx, 0.12, 0.10, 0.06, 0.42 * alpha);
    CGContextSetLineWidth(ctx, 1.0);
    CGContextStrokeRect(ctx, CGRectMake(x + 2, y + 2, size - 4, size - 4));
}

static void draw_block_with_offset(CGContextRef ctx, int gx, int gy,
                                   int color_index, double alpha,
                                   double vertical_offset) {
    double x = BOARD_X + gx * CELL;
    double y = BOARD_Y + (ROWS - 1 - gy) * CELL + vertical_offset;
    Color c = piece_colors[color_index];
    fill_rect(ctx, x + 2, y + 2, CELL - 4, CELL - 4, c, alpha);
    Color shine = {1.0, 1.0, 1.0};
    fill_rect(ctx, x + 5, y + CELL - 8, CELL - 10, 3, shine, 0.20 * alpha);
}

static void draw_block(CGContextRef ctx, int gx, int gy, int color_index,
                       double alpha) {
    draw_block_with_offset(ctx, gx, gy, color_index, alpha, 0.0);
}

static void draw_clearing_block(CGContextRef ctx, int gx, int gy,
                                int color_index) {
    double remaining = normal_clear_timer / 0.34;
    if (remaining < 0.0) remaining = 0.0;
    if (remaining > 1.0) remaining = 1.0;
    double progress = 1.0 - remaining;
    double local_remaining = remaining;
    double x_shift = 0.0;
    double width;
    double height;
    if (normal_clear_variant == 0) {
        double eased = remaining * remaining;
        width = (CELL - 4) * (0.10 + 0.90 * eased);
        height = (CELL - 4) * (0.35 + 0.65 * remaining);
    } else if (normal_clear_variant == 1) {
        width = (CELL - 4) * (0.72 + 0.28 * remaining);
        height = (CELL - 4) * (0.08 + 0.92 * remaining * remaining);
        x_shift = (gx % 2 ? 1.0 : -1.0) * progress * 11.0;
    } else if (normal_clear_variant == 2) {
        double distance = gx < 5 ? 4.5 - gx : gx - 4.5;
        double delayed = progress - distance * 0.045;
        if (delayed < 0.0) delayed = 0.0;
        if (delayed > 0.78) delayed = 0.78;
        local_remaining = 1.0 - delayed / 0.78;
        width = (CELL - 4) * (0.12 + 0.88 * local_remaining);
        height = width;
        x_shift = (gx < 5 ? -1.0 : 1.0) * (1.0 - local_remaining) * 8.0;
    } else {
        double delay = (double)((gx * 7 + gy * 3) % COLS) * 0.045;
        double dissolve = progress - delay;
        if (dissolve < 0.0) dissolve = 0.0;
        if (dissolve > 0.58) dissolve = 0.58;
        local_remaining = 1.0 - dissolve / 0.58;
        width = (CELL - 4) * (0.18 + 0.82 * local_remaining);
        height = (CELL - 4) * (0.18 + 0.82 * local_remaining);
        x_shift = (gx % 2 ? 1.0 : -1.0) * (1.0 - local_remaining) * 13.0;
    }
    double x = BOARD_X + gx * CELL + CELL / 2.0 - width / 2.0 + x_shift;
    double y = BOARD_Y + (ROWS - 1 - gy) * CELL + CELL / 2.0 - height / 2.0;
    Color color = piece_colors[color_index];
    fill_rect(ctx, x, y, width, height, color,
              0.28 + 0.72 * local_remaining);
    Color white = {1.0, 1.0, 1.0};
    fill_rect(ctx, x, y + height * 0.42, width, height * 0.18,
              white, (1.0 - local_remaining) * 0.76);
}

static void draw_piece(CGContextRef ctx, FallingPiece p, double alpha) {
    for (int i = 0; i < 4; ++i) {
        int x = p.x + shapes[p.type][p.rotation][i].x;
        int y = p.y + shapes[p.type][p.rotation][i].y;
        if (y >= 0) {
            if (minecraft_time > 0.0) {
                bool grass_top = true;
                for (int j = 0; j < 4; ++j) {
                    int other_x = p.x + shapes[p.type][p.rotation][j].x;
                    int other_y = p.y + shapes[p.type][p.rotation][j].y;
                    if (other_x == x && other_y == y - 1) grass_top = false;
                }
                double px = BOARD_X + x * CELL;
                double py = BOARD_Y + (ROWS - 1 - y) * CELL;
                draw_minecraft_tile(ctx, px, py, CELL, alpha, grass_top,
                                    (uint32_t)(p.type * 97 + x * 17 + y * 31));
            } else {
                draw_block(ctx, x, y, p.type + 1, alpha);
            }
            if (i == p.special_index) {
                double px = BOARD_X + x * CELL;
                double py = BOARD_Y + (ROWS - 1 - y) * CELL;
                draw_special_marker(ctx, px, py, CELL, p.special_type, alpha);
            }
        }
    }
}

static void draw_preview(CGContextRef ctx, int type, int special_index,
                         int special_type, double x, double y,
                         double box_width, double box_height, int size) {
    int min_x = 4, max_x = 0, min_y = 4, max_y = 0;
    for (int i = 0; i < 4; ++i) {
        Block b = shapes[type][0][i];
        if (b.x < min_x) min_x = b.x; if (b.x > max_x) max_x = b.x;
        if (b.y < min_y) min_y = b.y; if (b.y > max_y) max_y = b.y;
    }
    double width = (max_x - min_x + 1) * size;
    double height = (max_y - min_y + 1) * size;
    double ox = x + (box_width - width) / 2.0 - min_x * size;
    double oy = y + (box_height - height) / 2.0 - min_y * size;
    for (int i = 0; i < 4; ++i) {
        Block b = shapes[type][0][i];
        double px = ox + b.x * size;
        double py = oy + (max_y - b.y) * size;
        if (minecraft_time > 0.0) {
            bool grass_top = true;
            for (int j = 0; j < 4; ++j) {
                Block other = shapes[type][0][j];
                if (other.x == b.x && other.y == b.y - 1) grass_top = false;
            }
            draw_minecraft_tile(ctx, px, py, size, 1.0, grass_top,
                                (uint32_t)(type * 101 + b.x * 19 + b.y * 37));
        } else {
            Color c = piece_colors[type + 1];
            fill_rect(ctx, px + 2, py + 2, size - 4, size - 4, c, 1.0);
        }
        if (i == special_index)
            draw_special_marker(ctx, px, py, size, special_type, 1.0);
    }
}

static void draw_effects(CGContextRef ctx) {
    for (int y = 0; y < ROWS; ++y) {
        for (int x = 0; x < COLS; ++x) {
            if (effect_timer[y][x] <= 0.0) continue;
            double duration = 0.36;
            if (effect_kind[y][x] == SPECIAL_ROCKET) duration = 0.54;
            else if (effect_kind[y][x] == SPECIAL_METEOR) duration = 0.46;
            else if (effect_kind[y][x] == SPECIAL_PRISM) duration = 0.50;
            else if (effect_kind[y][x] == SPECIAL_DRILL) duration = 0.46;
            else if (effect_kind[y][x] == SPECIAL_DIAGONAL) duration = 0.44;
            else if (effect_kind[y][x] == SPECIAL_CROSS) duration = 0.42;
            else if (effect_kind[y][x] == SPECIAL_PULSE) duration = 0.48;
            else if (effect_kind[y][x] == SPECIAL_THUNDER) duration = 0.42;
            double alpha = effect_timer[y][x] / duration;
            if (alpha > 1.0) alpha = 1.0;
            int variant = effect_variant[y][x] % 3;
            double px = BOARD_X + x * CELL;
            double py = BOARD_Y + (ROWS - 1 - y) * CELL;
            if (effect_kind[y][x] == SPECIAL_BOMB) {
                Color fire = {1.0, 0.25, 0.05};
                Color core = {1.0, 0.90, 0.25};
                if (variant == 0) {
                    fill_rect(ctx, px + 1, py + 1, CELL - 2, CELL - 2,
                              fire, 0.76 * alpha);
                    CGContextSetRGBFillColor(ctx, core.r, core.g, core.b,
                                             0.9 * alpha);
                    CGContextFillEllipseInRect(ctx, CGRectMake(px + 7, py + 7,
                                                               CELL - 14, CELL - 14));
                } else if (variant == 1) {
                    fill_rect(ctx, px + 3, py + 3, CELL - 6, CELL - 6,
                              core, 0.72 * alpha);
                    fill_rect(ctx, px, py + CELL / 2.0 - 3, CELL, 6,
                              fire, alpha);
                    fill_rect(ctx, px + CELL / 2.0 - 3, py, 6, CELL,
                              fire, alpha);
                } else {
                    CGContextSetRGBStrokeColor(ctx, core.r, core.g, core.b, alpha);
                    CGContextSetLineWidth(ctx, 4.0);
                    CGContextStrokeEllipseInRect(ctx, CGRectMake(px + 2, py + 2,
                                                                 CELL - 4, CELL - 4));
                    fill_rect(ctx, px + 7, py + 7, CELL - 14, CELL - 14,
                              fire, 0.82 * alpha);
                }
            } else if (effect_kind[y][x] == SPECIAL_LASER) {
                Color beam = {0.15, 0.95, 1.0};
                Color white = {0.90, 1.0, 1.0};
                if (variant == 0) {
                    fill_rect(ctx, px + CELL / 2.0 - 8, py, 16, CELL,
                              beam, 0.36 * alpha);
                    fill_rect(ctx, px + CELL / 2.0 - 2, py, 5, CELL,
                              beam, alpha);
                } else if (variant == 1) {
                    fill_rect(ctx, px + CELL / 2.0 - 7, py, 4, CELL,
                              beam, 0.85 * alpha);
                    fill_rect(ctx, px + CELL / 2.0 + 3, py, 4, CELL,
                              beam, 0.85 * alpha);
                    fill_rect(ctx, px + 3, py + CELL / 2.0 - 2, CELL - 6, 4,
                              white, 0.72 * alpha);
                } else {
                    double pulse = ((y + (int)(visual_time * 28.0)) % 2) ? 1.0 : 0.48;
                    fill_rect(ctx, px + 2, py + 2, CELL - 4, CELL - 4,
                              beam, 0.26 * alpha * pulse);
                    fill_rect(ctx, px + CELL / 2.0 - 3, py, 6, CELL,
                              white, alpha * pulse);
                }
            } else if (effect_kind[y][x] == SPECIAL_CROSS) {
                Color arc = {0.78, 0.38, 1.0};
                fill_rect(ctx, px, py + CELL / 2.0 - 3, CELL, 6,
                          arc, 0.92 * alpha);
                fill_rect(ctx, px + CELL / 2.0 - 3, py, 6, CELL,
                          arc, 0.92 * alpha);
                if (variant == 1)
                    fill_rect(ctx, px + 4, py + 4, CELL - 8, CELL - 8,
                              (Color){1.0, 0.82, 1.0}, 0.28 * alpha);
            } else if (effect_kind[y][x] == SPECIAL_PRISM) {
                Color prism = piece_colors[1 + (x + y + variant) % PIECES];
                CGContextSetRGBFillColor(ctx, prism.r, prism.g, prism.b,
                                         0.72 * alpha);
                CGContextFillEllipseInRect(ctx, CGRectMake(px + 3, py + 3,
                                                           CELL - 6, CELL - 6));
                fill_rect(ctx, px + 4, py + CELL / 2.0 - 2,
                          CELL - 8, 4, (Color){1.0, 1.0, 1.0}, alpha);
            } else if (effect_kind[y][x] == SPECIAL_DIAGONAL) {
                Color slash = {0.32, 1.0, 0.55};
                CGContextSetRGBStrokeColor(ctx, slash.r, slash.g, slash.b, alpha);
                CGContextSetLineWidth(ctx, variant == 1 ? 7.0 : 4.0);
                CGContextMoveToPoint(ctx, px + 2, py + 2);
                CGContextAddLineToPoint(ctx, px + CELL - 2, py + CELL - 2);
                CGContextMoveToPoint(ctx, px + 2, py + CELL - 2);
                CGContextAddLineToPoint(ctx, px + CELL - 2, py + 2);
                CGContextStrokePath(ctx);
            } else if (effect_kind[y][x] == SPECIAL_DRILL) {
                Color drill = {1.0, 0.62, 0.14};
                fill_rect(ctx, px + 3, py + 2, CELL - 6, CELL - 4,
                          drill, 0.30 * alpha);
                CGContextSetRGBStrokeColor(ctx, 1.0, 0.92, 0.45, alpha);
                CGContextSetLineWidth(ctx, 4.0);
                CGContextMoveToPoint(ctx, px + 5, py + CELL - 7);
                CGContextAddLineToPoint(ctx, px + CELL / 2.0, py + 5);
                CGContextAddLineToPoint(ctx, px + CELL - 5, py + CELL - 7);
                CGContextStrokePath(ctx);
            } else if (effect_kind[y][x] == SPECIAL_PULSE) {
                Color pulse = {1.0, 0.84, 0.12};
                Color core = {1.0, 1.0, 0.72};
                CGContextSetRGBStrokeColor(ctx, pulse.r, pulse.g, pulse.b, alpha);
                CGContextSetLineWidth(ctx, variant == 1 ? 6.0 : 4.0);
                CGContextStrokeEllipseInRect(ctx, CGRectMake(px + 2, py + 2,
                                                             CELL - 4, CELL - 4));
                CGContextSetRGBFillColor(ctx, core.r, core.g, core.b,
                                         0.42 * alpha);
                CGContextFillEllipseInRect(ctx, CGRectMake(px + 8, py + 8,
                                                           CELL - 16, CELL - 16));
            } else if (effect_kind[y][x] == SPECIAL_THUNDER) {
                Color bolt = {0.65, 0.90, 1.0};
                fill_rect(ctx, px + 2, py + 2, CELL - 4, CELL - 4,
                          bolt, 0.20 * alpha);
                CGContextBeginPath(ctx);
                CGContextMoveToPoint(ctx, px + CELL * 0.62, py + CELL - 2);
                CGContextAddLineToPoint(ctx, px + CELL * 0.38, py + CELL * 0.55);
                CGContextAddLineToPoint(ctx, px + CELL * 0.58, py + CELL * 0.55);
                CGContextAddLineToPoint(ctx, px + CELL * 0.34, py + 2);
                CGContextSetRGBStrokeColor(ctx, 0.92, 1.0, 1.0, alpha);
                CGContextSetLineWidth(ctx, variant == 2 ? 6.0 : 4.0);
                CGContextStrokePath(ctx);
            } else if (effect_kind[y][x] == SPECIAL_ROCKET ||
                       effect_kind[y][x] == SPECIAL_METEOR) {
                bool meteor = effect_kind[y][x] == SPECIAL_METEOR;
                Color blast = meteor ? (Color){0.48, 0.18, 1.0}
                                     : (Color){1.0, 0.18, 0.04};
                Color hot = meteor ? (Color){0.82, 0.72, 1.0}
                                   : (Color){1.0, 0.92, 0.32};
                fill_rect(ctx, px, py, CELL, CELL, blast, 0.58 * alpha);
                CGContextSetRGBFillColor(ctx, hot.r, hot.g, hot.b, 0.88 * alpha);
                CGContextFillEllipseInRect(ctx, CGRectMake(px + 4, py + 4,
                                                           CELL - 8, CELL - 8));
            }
        }
    }
}

static void draw_rocket(CGContextRef ctx) {
    if (!rocket.active) return;
    double x = BOARD_X + (rocket.column + 0.5) * CELL;
    double y = BOARD_Y + (ROWS - rocket.y - 0.5) * CELL;
    Color glow = rocket.mode ? (Color){0.62, 0.28, 1.0}
                             : (Color){1.0, 0.28, 0.06};
    Color body = rocket.mode ? (Color){0.82, 0.75, 1.0}
                             : (Color){0.90, 0.94, 1.0};
    Color dark = {0.14, 0.18, 0.26};
    Color flame = rocket.mode ? (Color){0.40, 0.95, 1.0}
                              : (Color){1.0, 0.92, 0.24};

    CGContextSetRGBFillColor(ctx, glow.r, glow.g, glow.b, 0.24);
    CGContextFillEllipseInRect(ctx, CGRectMake(x - 16, y - 23, 32, 46));
    fill_rect(ctx, x - 8, y - 13, 16, 26, body, 1.0);
    fill_rect(ctx, x - 5, y - 8, 10, 12, dark, 1.0);

    CGContextBeginPath(ctx);
    CGContextMoveToPoint(ctx, x - 8, y - 13);
    CGContextAddLineToPoint(ctx, x + 8, y - 13);
    CGContextAddLineToPoint(ctx, x, y - 23);
    CGContextClosePath(ctx);
    CGContextSetRGBFillColor(ctx, glow.r, glow.g, glow.b, 1.0);
    CGContextFillPath(ctx);

    CGContextBeginPath(ctx);
    CGContextMoveToPoint(ctx, x - 8, y + 8);
    CGContextAddLineToPoint(ctx, x - 14, y + 16);
    CGContextAddLineToPoint(ctx, x - 6, y + 13);
    CGContextMoveToPoint(ctx, x + 8, y + 8);
    CGContextAddLineToPoint(ctx, x + 14, y + 16);
    CGContextAddLineToPoint(ctx, x + 6, y + 13);
    CGContextSetRGBStrokeColor(ctx, glow.r, glow.g, glow.b, 1.0);
    CGContextSetLineWidth(ctx, 4.0);
    CGContextStrokePath(ctx);

    CGContextBeginPath(ctx);
    CGContextMoveToPoint(ctx, x - 5, y + 13);
    double flicker = (double)((uint32_t)(visual_time * 50.0) % 6u);
    CGContextAddLineToPoint(ctx, x, y + 25 + flicker);
    CGContextAddLineToPoint(ctx, x + 5, y + 13);
    CGContextClosePath(ctx);
    CGContextSetRGBFillColor(ctx, flame.r, flame.g, flame.b, 0.95);
    CGContextFillPath(ctx);
}

static void draw_particles(CGContextRef ctx) {
    for (int i = 0; i < MAX_PARTICLES; ++i) {
        const Particle *p = &particles[i];
        if (!p->active) continue;
        double alpha = p->life / p->max_life;
        double size = p->size * (0.45 + 0.55 * alpha);
        CGContextBeginPath(ctx);
        CGContextMoveToPoint(ctx, p->x, p->y);
        CGContextAddLineToPoint(ctx, p->x - p->vx * 0.035,
                                p->y - p->vy * 0.035);
        CGContextSetRGBStrokeColor(ctx, p->color.r, p->color.g, p->color.b,
                                   alpha * 0.55);
        CGContextSetLineWidth(ctx, size * 0.55);
        CGContextStrokePath(ctx);
        fill_rect(ctx, p->x - size / 2.0, p->y - size / 2.0,
                  size, size, p->color, alpha);
        Color spark = {1.0, 1.0, 1.0};
        fill_rect(ctx, p->x - size / 4.0, p->y + size / 5.0,
                  size / 2.0, size / 3.0, spark, alpha * 0.45);
    }
}

static void draw_score_popups(CGContextRef ctx) {
    char number[20];
    for (int i = 0; i < MAX_SCORE_POPUPS; ++i) {
        const ScorePopup *popup = &score_popups[i];
        if (!popup->active) continue;
        double alpha = popup->life / popup->max_life;
        if (alpha < 0.0) alpha = 0.0;
        snprintf(number, sizeof(number), "%d", popup->points);
        int scale = popup->points >= 100 ? 3 : 2;
        double width = text_width(number, scale);
        double x = popup->x - width / 2.0;
        Color dark = {0.015, 0.025, 0.045};
        Color glow = popup->color;
        fill_rect(ctx, x - 5, popup->y - 4, width + 10, 7 * scale + 8,
                  glow, 0.16 * alpha);
        draw_text_alpha(ctx, number, x + 2, popup->y - 2,
                        scale, dark, 0.85 * alpha);
        draw_text_alpha(ctx, number, x, popup->y,
                        scale, popup->color, alpha);
    }
}

static void draw_normal_clear_sweep(CGContextRef ctx) {
    if (!normal_clear_active) return;
    double progress = 1.0 - normal_clear_timer / 0.34;
    if (progress < 0.0) progress = 0.0;
    if (progress > 1.0) progress = 1.0;
    Color glow = {1.0, 0.96, 0.72};
    for (int y = 0; y < ROWS; ++y) {
        if (!pending_clear_rows[y]) continue;
        double py = BOARD_Y + (ROWS - 1 - y) * CELL;
        if (normal_clear_variant == 0) {
            double sweep_x = BOARD_X - 22.0 + progress * (COLS * CELL + 44.0);
            fill_rect(ctx, sweep_x, py + 2, 30, CELL - 4, glow,
                      0.62 * (1.0 - progress));
        } else if (normal_clear_variant == 1) {
            double half = COLS * CELL / 2.0;
            double travel = progress * half;
            fill_rect(ctx, BOARD_X + half - travel - 9, py, 18, CELL,
                      glow, 0.55 * (1.0 - progress));
            fill_rect(ctx, BOARD_X + half + travel - 9, py, 18, CELL,
                      glow, 0.55 * (1.0 - progress));
        } else if (normal_clear_variant == 2) {
            for (int x = 0; x < COLS; ++x) {
                double phase = progress * 12.0 - x;
                if (phase < 0.0 || phase > 2.2) continue;
                double strength = phase < 1.1 ? phase / 1.1
                                              : (2.2 - phase) / 1.1;
                fill_rect(ctx, BOARD_X + x * CELL + 3, py + 3,
                          CELL - 6, CELL - 6, glow, 0.72 * strength);
            }
        } else {
            for (int x = 0; x < COLS; ++x) {
                double phase = progress * 15.0 - ((x * 7 + y * 3) % COLS);
                if (phase < 0.0 || phase > 3.0) continue;
                double strength = 1.0 - phase / 3.0;
                Color pixel = piece_colors[1 + (x + y) % PIECES];
                fill_rect(ctx, BOARD_X + x * CELL + 5,
                          py + 4 + (x % 3) * 6, CELL - 10, 5,
                          pixel, 0.85 * strength);
            }
        }
    }
}

static void draw_shockwaves(CGContextRef ctx) {
    for (int i = 0; i < MAX_WAVES; ++i) {
        const Shockwave *wave = &shockwaves[i];
        if (!wave->active) continue;
        double progress = 1.0 - wave->life / wave->max_life;
        double radius = 8.0 + progress * 38.0;
        Color color = {0.25, 0.95, 1.0};
        double line_width = 3.0;
        if (wave->type == SPECIAL_ROCKET) {
            radius = 18.0 + progress * 125.0;
            color = (Color){1.0, 0.28, 0.05};
            line_width = 7.0;
        } else if (wave->type == SPECIAL_METEOR) {
            radius = 16.0 + progress * 92.0;
            color = (Color){0.65, 0.34, 1.0};
            line_width = 6.0;
        } else if (wave->type == SPECIAL_PRISM) {
            radius = 12.0 + progress * 105.0;
            color = (Color){1.0, 0.38, 0.82};
            line_width = 4.0;
        } else if (wave->type == SPECIAL_BOMB) {
            radius = 12.0 + progress * 70.0;
            color = (Color){1.0, 0.55, 0.10};
            line_width = 5.0;
        } else if (wave->type == SPECIAL_CROSS) {
            radius = 10.0 + progress * 62.0;
            color = (Color){0.78, 0.38, 1.0};
            line_width = 4.0;
        } else if (wave->type == SPECIAL_DIAGONAL) {
            radius = 10.0 + progress * 72.0;
            color = (Color){0.32, 1.0, 0.55};
            line_width = 4.0;
        } else if (wave->type == SPECIAL_DRILL) {
            radius = 8.0 + progress * 55.0;
            color = (Color){1.0, 0.62, 0.14};
            line_width = 5.0;
        } else if (wave->type == SPECIAL_PULSE) {
            radius = 14.0 + progress * 82.0;
            color = (Color){1.0, 0.84, 0.14};
            line_width = 5.0;
        } else if (wave->type == SPECIAL_THUNDER) {
            radius = 9.0 + progress * 68.0;
            color = (Color){0.62, 0.90, 1.0};
            line_width = 4.0;
        }
        double alpha = (1.0 - progress) * 0.9;
        CGContextSetRGBStrokeColor(ctx, color.r, color.g, color.b, alpha);
        CGContextSetLineWidth(ctx, line_width);
        CGRect wave_rect = CGRectMake(wave->x - radius, wave->y - radius,
                                      radius * 2.0, radius * 2.0);
        if (wave->variant == 1 && wave->type != SPECIAL_ROCKET)
            CGContextStrokeRect(ctx, wave_rect);
        else
            CGContextStrokeEllipseInRect(ctx, wave_rect);
        double echo = radius * 1.22;
        CGContextSetRGBStrokeColor(ctx, color.r, color.g, color.b, alpha * 0.34);
        CGContextSetLineWidth(ctx, 2.0);
        CGContextStrokeEllipseInRect(ctx, CGRectMake(wave->x - echo,
            wave->y - echo, echo * 2.0, echo * 2.0));
        double far_echo = radius * 1.48;
        CGContextSetRGBStrokeColor(ctx, 1.0, 1.0, 1.0, alpha * 0.16);
        CGContextSetLineWidth(ctx, 1.5);
        CGContextStrokeEllipseInRect(ctx, CGRectMake(wave->x - far_echo,
            wave->y - far_echo, far_echo * 2.0, far_echo * 2.0));
        if (wave->type == SPECIAL_BOMB || wave->type == SPECIAL_ROCKET ||
            wave->type == SPECIAL_METEOR) {
            double ray = radius * 1.10;
            CGContextBeginPath(ctx);
            CGContextMoveToPoint(ctx, wave->x - ray, wave->y - ray);
            CGContextAddLineToPoint(ctx, wave->x + ray, wave->y + ray);
            CGContextMoveToPoint(ctx, wave->x - ray, wave->y + ray);
            CGContextAddLineToPoint(ctx, wave->x + ray, wave->y - ray);
            CGContextSetRGBStrokeColor(ctx, color.r, color.g, color.b,
                                       alpha * 0.46);
            CGContextSetLineWidth(ctx, 3.0);
            CGContextStrokePath(ctx);
        }
        if (wave->variant == 2) {
            CGContextSetLineWidth(ctx, 3.0);
            CGContextMoveToPoint(ctx, wave->x - radius, wave->y);
            CGContextAddLineToPoint(ctx, wave->x + radius, wave->y);
            CGContextMoveToPoint(ctx, wave->x, wave->y - radius);
            CGContextAddLineToPoint(ctx, wave->x, wave->y + radius);
            CGContextStrokePath(ctx);
        }
        if (wave->type == SPECIAL_BOMB || wave->type == SPECIAL_ROCKET ||
            wave->type == SPECIAL_METEOR || wave->type == SPECIAL_PRISM ||
            wave->type == SPECIAL_PULSE) {
            double inner = radius * 0.58;
            CGContextSetRGBStrokeColor(ctx, 1.0, 0.95, 0.55, alpha * 0.65);
            CGContextSetLineWidth(ctx, 2.0);
            CGContextStrokeEllipseInRect(ctx, CGRectMake(wave->x - inner,
                wave->y - inner, inner * 2.0, inner * 2.0));
        }
    }
}

static void render_game(CGContextRef ctx) {
    Color background = {0.035, 0.045, 0.075};
    Color panel = {0.065, 0.085, 0.13};
    Color border = {0.18, 0.24, 0.34};
    Color white = {0.92, 0.95, 1.0};
    Color muted = {0.46, 0.55, 0.68};
    Color accent = {0.20, 0.82, 0.92};

    fill_rect(ctx, 0, 0, WINDOW_W, WINDOW_H, background, 1.0);

    double shake_x = 0.0, shake_y = 0.0;
    if (shake_time > 0.0) {
        uint32_t frame = (uint32_t)(visual_time * 120.0);
        uint32_t hash_x = frame * 1664525u + 1013904223u;
        uint32_t hash_y = hash_x * 22695477u + 1u;
        double fade = shake_time / 0.30;
        if (fade > 1.0) fade = 1.0;
        shake_x = ((double)(hash_x % 2001u) / 1000.0 - 1.0) *
                  shake_strength * fade;
        shake_y = ((double)(hash_y % 2001u) / 1000.0 - 1.0) *
                  shake_strength * fade;
    }
    CGContextSaveGState(ctx);
    CGContextTranslateCTM(ctx, shake_x, shake_y + board_rise_offset);

    fill_rect(ctx, BOARD_X - 5, BOARD_Y - 5, COLS * CELL + 10,
              ROWS * CELL + 10, border, 1.0);
    if (focus_time > 0.0) {
        double pulse = ((uint32_t)(visual_time * 8.0) % 2u) ? 0.95 : 0.58;
        CGContextSetRGBStrokeColor(ctx, 1.0, 0.82, 0.22, pulse);
        CGContextSetLineWidth(ctx, 4.0);
        CGContextStrokeRect(ctx, CGRectMake(BOARD_X - 8, BOARD_Y - 8,
                                             COLS * CELL + 16,
                                             ROWS * CELL + 16));
    }
    if (overdrive_time > 0.0) {
        double pulse = 0.50 + 0.35 * (double)((uint32_t)(visual_time * 12.0) % 2u);
        CGContextSetRGBStrokeColor(ctx, 0.35, 0.92, 1.0, pulse);
        CGContextSetLineWidth(ctx, 3.0);
        CGContextStrokeRect(ctx, CGRectMake(BOARD_X - 11, BOARD_Y - 11,
                                             COLS * CELL + 22,
                                             ROWS * CELL + 22));
    }
    if (rescue_shield) {
        double shield_alpha = ((uint32_t)(visual_time * 6.0) % 2u) ? 0.82 : 0.48;
        CGContextSetRGBStrokeColor(ctx, 0.35, 1.0, 0.72, shield_alpha);
        CGContextSetLineWidth(ctx, 3.0);
        CGContextStrokeRect(ctx, CGRectMake(BOARD_X - 14, BOARD_Y - 14,
                                             COLS * CELL + 28,
                                             ROWS * CELL + 28));
    }
    if (minecraft_time > 0.0) {
        double grass_alpha = ((uint32_t)(visual_time * 8.0) % 2u) ? 0.95 : 0.68;
        CGContextSetRGBStrokeColor(ctx, 0.30, 0.76, 0.16, grass_alpha);
        CGContextSetLineWidth(ctx, 5.0);
        CGContextStrokeRect(ctx, CGRectMake(BOARD_X - 17, BOARD_Y - 17,
                                             COLS * CELL + 34,
                                             ROWS * CELL + 34));
        CGContextSetRGBStrokeColor(ctx, 0.48, 0.28, 0.12, 0.88);
        CGContextSetLineWidth(ctx, 3.0);
        CGContextStrokeRect(ctx, CGRectMake(BOARD_X - 21, BOARD_Y - 21,
                                             COLS * CELL + 42,
                                             ROWS * CELL + 42));
    }
    fill_rect(ctx, BOARD_X, BOARD_Y, COLS * CELL, ROWS * CELL, panel, 1.0);

    Color grid = {0.12, 0.15, 0.21};
    CGContextSetRGBStrokeColor(ctx, grid.r, grid.g, grid.b, 1.0);
    CGContextSetLineWidth(ctx, 1.0);
    for (int x = 0; x <= COLS; ++x) {
        CGContextMoveToPoint(ctx, BOARD_X + x * CELL, BOARD_Y);
        CGContextAddLineToPoint(ctx, BOARD_X + x * CELL, BOARD_Y + ROWS * CELL);
    }
    for (int y = 0; y <= ROWS; ++y) {
        CGContextMoveToPoint(ctx, BOARD_X, BOARD_Y + y * CELL);
        CGContextAddLineToPoint(ctx, BOARD_X + COLS * CELL, BOARD_Y + y * CELL);
    }
    CGContextStrokePath(ctx);

    for (int y = 0; y < ROWS; ++y) {
        for (int x = 0; x < COLS; ++x) {
            if (board[y][x]) {
                if (normal_clear_active && pending_clear_rows[y])
                    draw_clearing_block(ctx, x, y, board[y][x]);
                else if (minecraft_time > 0.0) {
                    double px = BOARD_X + x * CELL;
                    double py = BOARD_Y + (ROWS - 1 - y) * CELL +
                                fall_offset[y][x];
                    bool grass_top = y == 0 || board[y - 1][x] == 0;
                    draw_minecraft_tile(ctx, px, py, CELL, 1.0, grass_top,
                                        (uint32_t)(x * 43 + y * 71 +
                                                   board[y][x] * 113));
                } else
                    draw_block_with_offset(ctx, x, y, board[y][x], 1.0,
                                           fall_offset[y][x]);
                if (board_special[y][x] != SPECIAL_NONE) {
                    double px = BOARD_X + x * CELL;
                    double py = BOARD_Y + (ROWS - 1 - y) * CELL +
                                fall_offset[y][x];
                    draw_special_marker(ctx, px, py, CELL,
                                        board_special[y][x], 1.0);
                }
            }
        }
    }
    draw_normal_clear_sweep(ctx);

    if (!game_over && !rocket.active && !normal_clear_active &&
        !waiting_for_settle) {
        FallingPiece ghost = current;
        while (can_place(ghost.type, ghost.rotation, ghost.x, ghost.y + 1)) ++ghost.y;
        draw_piece(ctx, ghost, 0.20);
        draw_piece(ctx, current, 1.0);
    }
    draw_rocket(ctx);
    draw_effects(ctx);
    draw_shockwaves(ctx);
    draw_particles(ctx);

    if (flash_time > 0.0) {
        Color flash = flash_kind == SPECIAL_ROCKET
            ? (Color){1.0, 0.50, 0.16}
            : (flash_kind == SPECIAL_METEOR ? (Color){0.62, 0.40, 1.0}
            : (flash_kind == SPECIAL_PRISM ? (Color){1.0, 0.45, 0.88}
            : (flash_kind == SPECIAL_CROSS ? (Color){0.72, 0.42, 1.0}
            : (flash_kind == SPECIAL_BOMB
                ? (Color){1.0, 0.72, 0.25} : (Color){0.45, 0.95, 1.0}))));
        double maximum = flash_kind == SPECIAL_ROCKET ? 0.20
            : (flash_kind == SPECIAL_METEOR ? 0.18
            : (flash_kind == SPECIAL_PRISM ? 0.20
            : (flash_kind == SPECIAL_BOMB ? 0.18 : 0.14)));
        if (flash_kind == SPECIAL_DIAGONAL) flash = (Color){0.35, 1.0, 0.58};
        if (flash_kind == SPECIAL_DRILL) flash = (Color){1.0, 0.62, 0.14};
        if (flash_kind == SPECIAL_PULSE) flash = (Color){1.0, 0.86, 0.18};
        if (flash_kind == SPECIAL_THUNDER) flash = (Color){0.60, 0.90, 1.0};
        if (flash_kind == SPECIAL_PULSE) maximum = 0.17;
        double alpha = flash_time / maximum;
        if (alpha > 1.0) alpha = 1.0;
        fill_rect(ctx, BOARD_X, BOARD_Y, COLS * CELL, ROWS * CELL,
                  flash, alpha * 0.50);
    }
    if (danger_flash_time > 0.0) {
        double alpha = danger_flash_time / 0.22;
        fill_rect(ctx, BOARD_X, BOARD_Y, COLS * CELL, ROWS * CELL,
                  (Color){1.0, 0.12, 0.08}, alpha * 0.30);
    }
    if (minecraft_flash_time > 0.0) {
        double alpha = minecraft_flash_time / 0.45;
        fill_rect(ctx, BOARD_X, BOARD_Y, COLS * CELL, ROWS * CELL,
                  (Color){0.30, 0.78, 0.16}, alpha * 0.44);
    }
    draw_score_popups(ctx);
    CGContextRestoreGState(ctx);

    if ((rocket.active && rocket.mode) || meteor_shower_remaining > 0)
        draw_centered(ctx, "METEOR STORM", BOARD_X + COLS * CELL / 2.0,
                      684, 2, (Color){0.72, 0.46, 1.0});
    if (danger_event_timer > 0.0)
        draw_centered(ctx, "GARBAGE RISE", BOARD_X + COLS * CELL / 2.0,
                      684, 2, (Color){1.0, 0.32, 0.20});
    if (perfect_clear_timer > 0.0)
        draw_centered(ctx, "PERFECT CLEAR", BOARD_X + COLS * CELL / 2.0,
                      BOARD_Y + ROWS * CELL / 2.0, 3,
                      (Color){1.0, 0.86, 0.24});
    if (chain_display_timer > 0.0 && cascade_chain > 0) {
        char chain_text[24];
        snprintf(chain_text, sizeof(chain_text), "CHAIN %dX", cascade_chain + 1);
        Color chain_color = {1.0, 0.82, 0.28};
        draw_centered(ctx, chain_text, BOARD_X + COLS * CELL / 2.0,
                      BOARD_Y + ROWS * CELL - 42, 3, chain_color);
    }
    if (flow_display_timer > 0.0 && flow_streak > 0) {
        char flow_text[24];
        snprintf(flow_text, sizeof(flow_text), "FLOW %dX", flow_streak);
        draw_centered(ctx, flow_text, BOARD_X + COLS * CELL / 2.0,
                      BOARD_Y + ROWS * CELL - 132, 3,
                      (Color){0.42, 1.0, 0.82});
    }
    if (focus_time > 0.0)
        draw_centered(ctx, "FOCUS 2X", BOARD_X + COLS * CELL / 2.0,
                      BOARD_Y + ROWS * CELL - 72, 3,
                      (Color){1.0, 0.84, 0.24});
    if (overdrive_banner_timer > 0.0)
        draw_centered(ctx, "OVERDRIVE", BOARD_X + COLS * CELL / 2.0,
                      BOARD_Y + ROWS * CELL / 2.0 + 42, 4,
                      (Color){0.62, 0.94, 1.0});
    if (overdrive_time > 0.0) {
        char overdrive_text[24];
        snprintf(overdrive_text, sizeof(overdrive_text), "OVERDRIVE %d",
                 (int)overdrive_time + 1);
        draw_centered(ctx, overdrive_text, BOARD_X + COLS * CELL / 2.0,
                      BOARD_Y + ROWS * CELL - 102, 2,
                      (Color){0.55, 0.92, 1.0});
    }
    if (minecraft_banner_timer > 0.0)
        draw_centered(ctx, "MINECRAFT", BOARD_X + COLS * CELL / 2.0,
                      BOARD_Y + ROWS * CELL / 2.0 + 76, 4,
                      (Color){0.48, 0.88, 0.24});
    if (minecraft_time > 0.0) {
        char minecraft_text[28];
        snprintf(minecraft_text, sizeof(minecraft_text), "MINECRAFT X2 %d",
                 (int)minecraft_time + 1);
        draw_centered(ctx, minecraft_text, BOARD_X + COLS * CELL / 2.0,
                      BOARD_Y + ROWS * CELL - 162, 2,
                      (Color){0.52, 0.92, 0.28});
    }
    if (shield_banner_timer > 0.0)
        draw_centered(ctx, rescue_shield ? "SHIELD READY" : "SHIELD SAVE",
                      BOARD_X + COLS * CELL / 2.0,
                      BOARD_Y + ROWS * CELL / 2.0 - 24, 3,
                      (Color){0.38, 1.0, 0.74});

    const double side_x = 395;
    draw_text(ctx, "TETRIS", side_x, 625, 7, accent);
    draw_text(ctx, "SCORE", side_x, 555, 3, muted);
    char number[32];
    snprintf(number, sizeof(number), "%d", score);
    int score_scale = strlen(number) <= 6 ? 5 : 4;
    double score_x = side_x + (220.0 - text_width(number, score_scale)) / 2.0;
    Color score_shadow = {0.01, 0.02, 0.04};
    fill_rect(ctx, side_x, 503, 220, 47, panel, 0.72);
    draw_text(ctx, number, score_x + 2, 511, score_scale, score_shadow);
    Color live_score = minecraft_time > 0.0 ? (Color){0.50, 0.90, 0.26}
        : (overdrive_time > 0.0 ? (Color){0.55, 0.94, 1.0}
        : (focus_time > 0.0 ? (Color){1.0, 0.84, 0.24} : white));
    draw_text(ctx, number, score_x, 513, score_scale, live_score);
    draw_text(ctx, "LINES", side_x, 474, 2, muted);
    snprintf(number, sizeof(number), "%d", lines);
    draw_text(ctx, number, side_x, 444, 3, white);
    draw_text(ctx, "LEVEL", 472, 474, 2, muted);
    snprintf(number, sizeof(number), "%d", level);
    draw_text(ctx, number, 472, 444, 3, white);
    draw_text(ctx, "BEST", 560, 474, 2, (Color){1.0, 0.84, 0.24});
    snprintf(number, sizeof(number), "%d", high_score);
    int best_scale = strlen(number) <= 7 ? 2 : 1;
    double best_x = side_x + 220.0 - text_width(number, best_scale);
    draw_text(ctx, number, best_x, 446, best_scale,
              (Color){1.0, 0.90, 0.40});

    draw_text(ctx, "NEXT", side_x, 390, 3, muted);
    fill_rect(ctx, side_x, 285, 220, 90, panel, 1.0);
    draw_preview(ctx, next_piece, next_special_index, next_special_type,
                 side_x, 285, 220, 90, 22);

    draw_text(ctx, minecraft_time > 0.0 ? "MINECRAFT X2" : "8 SPECIALS",
              side_x, 252, 2,
              minecraft_time > 0.0 ? (Color){0.50, 0.90, 0.26}
                                   : piece_colors[5]);
    draw_text(ctx, rescue_shield ? "SHIELD READY" : "FLOW BONUS",
              rescue_shield ? 515 : 525, 252, 2,
              rescue_shield ? (Color){0.38, 1.0, 0.74} : piece_colors[1]);
    draw_text(ctx, "CONTROLS", side_x, 220, 3, muted);
    draw_text(ctx, "A D     MOVE", side_x, 194, 2, white);
    draw_text(ctx, "S       DOWN", side_x, 174, 2, white);
    draw_text(ctx, "W X     ROTATE", side_x, 154, 2, white);
    draw_text(ctx, "SPACE   DROP", side_x, 134, 2, white);
    draw_text(ctx, "P       PAUSE", side_x, 114, 2, white);
    draw_text(ctx, "R       RESTART", side_x, 94, 2, white);
    draw_text(ctx, "E       FOCUS", side_x, 74, 2,
              focus_charge >= 100.0 || focus_time > 0.0
                  ? (Color){1.0, 0.84, 0.24} : muted);
    Color meter_border = {0.22, 0.28, 0.38};
    fill_rect(ctx, side_x, 18, 220, 14, meter_border, 1.0);
    double meter_ratio = focus_time > 0.0 ? focus_time / 8.0
                                         : focus_charge / 100.0;
    Color meter_color = focus_time > 0.0
        ? (Color){1.0, 0.72, 0.16} : (Color){0.25, 0.78, 0.95};
    fill_rect(ctx, side_x + 2, 20, 216 * meter_ratio, 10,
              meter_color, 1.0);

    if (paused || game_over) {
        Color overlay = {0.02, 0.025, 0.045};
        fill_rect(ctx, BOARD_X, BOARD_Y + 235, COLS * CELL, 130, overlay, 0.92);
        if (game_over) {
            draw_centered(ctx, "GAME OVER", BOARD_X + COLS * CELL / 2.0,
                          BOARD_Y + 310, 4, piece_colors[5]);
            draw_centered(ctx, "PRESS R", BOARD_X + COLS * CELL / 2.0,
                          BOARD_Y + 270, 3, white);
        } else {
            draw_centered(ctx, "PAUSED", BOARD_X + COLS * CELL / 2.0,
                          BOARD_Y + 290, 4, white);
        }
    }
}

static void draw_view(id self, SEL command, CGRect dirty_rect) {
    (void)self; (void)command; (void)dirty_rect;
    Class graphics_context = (Class)objc_getClass("NSGraphicsContext");
    id ns_context = ((id (*)(id, SEL))objc_msgSend)((id)graphics_context,
                                                    sel_registerName("currentContext"));
    CGContextRef context = ((CGContextRef (*)(id, SEL))objc_msgSend)(
        ns_context, sel_registerName("CGContext"));
    render_game(context);
}

static signed char accepts_first_responder(id self, SEL command) {
    (void)self; (void)command;
    return 1;
}

static id send_id(id object, const char *selector) {
    return ((id (*)(id, SEL))objc_msgSend)(object, sel_registerName(selector));
}

static void send_void(id object, const char *selector) {
    ((void (*)(id, SEL))objc_msgSend)(object, sel_registerName(selector));
}

int main(void) {
    srand((unsigned int)time(NULL));
    load_high_score();
    reset_game();

    Class pool_class = (Class)objc_getClass("NSAutoreleasePool");
    id outer_pool = send_id(send_id((id)pool_class, "alloc"), "init");
    Class app_class = (Class)objc_getClass("NSApplication");
    id app = send_id((id)app_class, "sharedApplication");
    ((void (*)(id, SEL, long))objc_msgSend)(app,
        sel_registerName("setActivationPolicy:"), 0L);

    Class base_view = (Class)objc_getClass("NSView");
    Class view_class = objc_allocateClassPair(base_view, "CTetrisView", 0);
    if (view_class) {
        class_addMethod(view_class, sel_registerName("drawRect:"), (IMP)draw_view,
                        "v@:{CGRect={CGPoint=dd}{CGSize=dd}}");
        class_addMethod(view_class, sel_registerName("acceptsFirstResponder"),
                        (IMP)accepts_first_responder, "c@:");
        objc_registerClassPair(view_class);
    } else {
        view_class = (Class)objc_getClass("CTetrisView");
    }

    CGRect frame = CGRectMake(0, 0, WINDOW_W, WINDOW_H);
    id view = ((id (*)(id, SEL, CGRect))objc_msgSend)(
        send_id((id)view_class, "alloc"), sel_registerName("initWithFrame:"), frame);

    Class window_class = (Class)objc_getClass("NSWindow");
    id window_alloc = send_id((id)window_class, "alloc");
    unsigned long styles = (1ul << 0) | (1ul << 1) | (1ul << 2);
    id window = ((id (*)(id, SEL, CGRect, unsigned long, unsigned long, signed char))objc_msgSend)(
        window_alloc, sel_registerName("initWithContentRect:styleMask:backing:defer:"),
        frame, styles, 2ul, 0);

    Class string_class = (Class)objc_getClass("NSString");
    id title = ((id (*)(id, SEL, const char *))objc_msgSend)(
        (id)string_class, sel_registerName("stringWithUTF8String:"), "Tetris in C");
    ((void (*)(id, SEL, id))objc_msgSend)(window, sel_registerName("setTitle:"), title);
    ((void (*)(id, SEL, signed char))objc_msgSend)(window,
        sel_registerName("setReleasedWhenClosed:"), 0);
    ((void (*)(id, SEL, id))objc_msgSend)(window, sel_registerName("setContentView:"), view);
    send_void(window, "center");
    ((void (*)(id, SEL, id))objc_msgSend)(window,
        sel_registerName("makeKeyAndOrderFront:"), (id)0);
    ((void (*)(id, SEL, id))objc_msgSend)(window,
        sel_registerName("makeFirstResponder:"), view);
    send_void(app, "finishLaunching");
    ((void (*)(id, SEL, signed char))objc_msgSend)(app,
        sel_registerName("activateIgnoringOtherApps:"), 1);

    id distant_past = send_id((id)objc_getClass("NSDate"), "distantPast");
    id run_mode = ((id (*)(id, SEL, const char *))objc_msgSend)(
        (id)string_class, sel_registerName("stringWithUTF8String:"),
        "kCFRunLoopDefaultMode");
    SEL next_event_sel = sel_registerName(
        "nextEventMatchingMask:untilDate:inMode:dequeue:");
    uint64_t previous = monotonic_ns();

    while (running) {
        id loop_pool = send_id(send_id((id)pool_class, "alloc"), "init");
        id event;
        while ((event = ((id (*)(id, SEL, unsigned long, id, id, signed char))objc_msgSend)(
                    app, next_event_sel, ~0ul, distant_past, run_mode, 1))) {
            unsigned long type = ((unsigned long (*)(id, SEL))objc_msgSend)(
                event, sel_registerName("type"));
            if (type == 10) {
                unsigned short key = ((unsigned short (*)(id, SEL))objc_msgSend)(
                    event, sel_registerName("keyCode"));
                handle_key(key);
            }
            ((void (*)(id, SEL, id))objc_msgSend)(app, sel_registerName("sendEvent:"), event);
        }

        uint64_t now = monotonic_ns();
        double dt = (double)(now - previous) / 1000000000.0;
        previous = now;
        if (dt > 0.1) dt = 0.1;
        update_game(dt);
        send_void(view, "display");

        signed char visible = ((signed char (*)(id, SEL))objc_msgSend)(
            window, sel_registerName("isVisible"));
        if (!visible) running = false;
        send_void(loop_pool, "drain");
        usleep(8000);
    }

    ((void (*)(id, SEL, id))objc_msgSend)(window, sel_registerName("orderOut:"), (id)0);
    send_void(view, "release");
    send_void(window, "release");
    send_void(outer_pool, "drain");
    save_high_score();
    return 0;
}
