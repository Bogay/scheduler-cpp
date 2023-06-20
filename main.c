#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <stddef.h>
#include <limits.h>
#include <stdint.h>
#include <assert.h>

#define MAX_ROOMS 16
#define NO_ASSIGN -1

typedef struct Room
{
    char *name;
    int cap;
} Room;

typedef struct Section
{
    int **staffs;
    size_t len;
} Section;

Room *gen_rooms(size_t r, size_t n)
{
    size_t cap = ceil((double)n / r);
    Room *rooms = (Room *)malloc(sizeof(Room) * r);
    for (size_t i = 0; i < r; i++)
    {
        char *name = (char *)malloc(sizeof(char) * 10);
        sprintf(name, "Room %lu", i);
        rooms[i].name = name;
        rooms[i].cap = cap;
    }
    return rooms;
}

int min_int(int a, int b)
{
    return a < b ? a : b;
}

void shuffle_int_arr(int *arr, int n)
{
    for (int i = n - 1; i > 0; i--)
    {
        int j = rand() % (i + 1);
        int temp = arr[i];
        arr[i] = arr[j];
        arr[j] = temp;
    }
}

int weight_fn(int i, int *c, Room *rooms, int room_id, int n, int *acc, int **weights, int **assigned_room)
{
    const int REASSIGN_BONUS = 10000000;
    int paired_penalty = 0;
    for (int j = 0; j < n; j++)
    {
        paired_penalty += weights[i][j];
    }
    int reassigned_penalty = (assigned_room[i][room_id] * REASSIGN_BONUS * 10);
    int same_cap_rooms[MAX_ROOMS] = {0};
    for (int j = 0; j < n; j++)
    {
        if (rooms[j].cap == rooms[room_id].cap)
        {
            same_cap_rooms[j] = 1;
        }
    }
    int reassigned_same_cap_penalty = 0;
    for (int j = 0; j < n; j++)
    {
        reassigned_same_cap_penalty += (assigned_room[i][j] * same_cap_rooms[j] * REASSIGN_BONUS);
    }
    int cap_penalty = REASSIGN_BONUS * 100 * min_int(n, (int)(sizeof(c) / sizeof(int)));
    int acc_penalty = (acc[room_id] * REASSIGN_BONUS);
    for (int j = 0; j < n; j++)
    {
        if (c[j] == NO_ASSIGN)
            break;
        acc_penalty += (c[j] * REASSIGN_BONUS);
    }
    int penalty = paired_penalty + cap_penalty + reassigned_penalty + reassigned_same_cap_penalty + acc_penalty;
    return penalty;
}

int **allocate_matrix(int rows, int cols)
{
    int **matrix = malloc(rows * sizeof(int *));
    assert(matrix != NULL);
    for (int i = 0; i < rows; ++i)
    {
        matrix[i] = malloc(cols * sizeof(int));
        assert(matrix[i] != NULL);
        for (size_t j = 0; j < cols; j++)
        {
            matrix[i][j] = NO_ASSIGN;
        }
    }
    return matrix;
}

void free_matrix(int **matrix, int rows)
{
    for (int i = 0; i < rows; ++i)
    {
        free(matrix[i]);
    }
    free(matrix);
}

size_t size(int *staffs)
{
    size_t s = 0;
    while (staffs != NULL && *staffs != NO_ASSIGN)
    {
        s++;
        staffs++;
    }
    return s;
}

void push_back(int *staffs, int staff)
{
    while (staffs != NULL && *staffs != NO_ASSIGN)
    {
        staffs++;
    }
    *staffs = staff;
}

int pop_back(int *staffs)
{
    int ret = *staffs;
    *staffs = NO_ASSIGN;
    return ret;
}

void shuffle(int *staffs, size_t n)
{
    // TODO
}

Section *solve(Room *rooms, size_t num_rooms, int t, int n)
{
    Section *secs = (Section *)malloc(t * sizeof(Section));
    int **weights = (int **)malloc(n * sizeof(int *));
    for (int i = 0; i < n; i++)
    {
        weights[i] = (int *)calloc(n, sizeof(int));
    }
    int *acc = (int *)calloc(num_rooms, sizeof(int));
    int **assigned_room = (int **)calloc(n, sizeof(int *));
    for (int i = 0; i < n; i++)
    {
        assigned_room[i] = (int *)calloc(num_rooms, sizeof(int));
    }

    for (int i = 0; i < t; i++)
    {
        int *used = (int *)calloc(n, sizeof(int));
        Section sec;
        sec.staffs = allocate_matrix(num_rooms, n);
        sec.len = num_rooms;

        // determine where to assign staff i
        int *staffs = (int *)malloc(n * sizeof(int));
        for (int j = 0; j < n; j++)
        {
            staffs[j] = j;
        }
        shuffle(staffs, n);

        for (int j = 0; j < n; j++)
        {
            int staff = staffs[j];

            int picked_room_id = -1;
            int min_penalty = INT_MAX;
            for (int room_id = 0; room_id < num_rooms; room_id++)
            {
                // printf("j = %d, room_id = %d\n", j, room_id);
                if (size(sec.staffs[room_id]) < rooms[room_id].cap)
                {
                    int penalty = weight_fn(staff, sec.staffs[room_id], rooms, room_id, n, acc, weights, assigned_room);
                    if (penalty < min_penalty)
                    {
                        min_penalty = penalty;
                        picked_room_id = room_id;
                    }
                }
            }

            assert(picked_room_id != -1);
            // printf("%d ", picked_room_id);
            // printf("%ld\n", size(sec.staffs[picked_room_id]));

            for (int p = 0, sz = size(sec.staffs[picked_room_id]); p < sz; p++)
            {
                int q = sec.staffs[picked_room_id][p];
                weights[i][q] += 1;
                weights[q][i] += 1;
            }
            used[staff] = 1;
            assigned_room[staff][picked_room_id] += 1;
            push_back(sec.staffs[picked_room_id], staff);
            acc[picked_room_id] += 1;
        }

        secs[i] = sec;

        free(staffs);
        free(used);
    }

    free(weights);
    free(acc);
    free(assigned_room);

    return secs;
}

size_t energy(const Section *results, const size_t r_len)
{
    size_t acc = 0;
    size_t n = 0;
    for (size_t i = 0; i < results[0].len; i++)
    {
        n += size(results[0].staffs[i]);
    }
    size_t len = results[0].len;
    size_t *count = (size_t *)calloc(len, sizeof(size_t));
    for (size_t s = 0; s < n; s++)
    {
        for (size_t j = 0; j < r_len; j++)
        {
            for (size_t k = 0; k < len; k++)
            {
                size_t s_len = size(results[j].staffs[k]);
                for (size_t p = 0; p < s_len; p++)
                {
                    if (results[j].staffs[k][p] == s)
                    {
                        count[k]++;
                        break;
                    }
                }
            }
        }
        for (size_t k = 0; k < len; k++)
        {
            acc += count[k] * count[k];
        }
        // reset count
        for (size_t k = 0; k < len; k++)
        {
            count[k] = 0;
        }
    }

    free(count);

    return acc;
}

size_t energy2(const Section *results, const size_t res_len, const Room *rooms, const size_t rm_len)
{
    size_t acc = energy(results, res_len);

    // printf("res_len, rm_len = %ld %ld\n", res_len, rm_len);

    for (size_t i = 0; i < res_len; i++)
    {
        int mn = -1, mx = -1;
        for (size_t j = 0; j < rm_len; j++)
        {
            // printf("i, j = %ld %ld\n", i, j);
            size_t tmp = rooms[j].cap - size(results[i].staffs[j]);
            if (mn == -1 || tmp < mn)
                mn = tmp;
            if (mx == -1 || tmp > mx)
                mx = tmp;
        }
        acc += mx * (mx - mn);
    }

    return acc;
}

// move results to ret
int neighbor(Section *results, size_t res_len, Section **ret, size_t *ret_len)
{
    size_t iter = rand() % 3 + 1;
    for (size_t i = 0; i < iter; i++)
    {
        Section *sec = results + (rand() % res_len);

        size_t max_retry = 64;
        size_t a = rand() % sec->len;
        size_t b = rand() % sec->len;
        while (a == b && max_retry--)
        {
            b = rand() % sec->len;
        }
        // fail
        if (a == b)
            return -1;

        // printf("a, b = %ld %ld\n", a, b);

        size_t a_len = size(sec->staffs[a]);
        size_t b_len = size(sec->staffs[b]);
        size_t l = sec->staffs[a][a_len - 1];
        size_t r = sec->staffs[b][b_len - 1];
        for (int j = a_len - 1; j > 0; j--)
        {
            sec->staffs[a][j] = sec->staffs[a][j - 1];
        }
        sec->staffs[a][0] = r;
        for (int j = b_len - 1; j > 0; j--)
        {
            sec->staffs[b][j] = sec->staffs[b][j - 1];
        }
        sec->staffs[b][0] = l;
    }

    *ret = results;
    *ret_len = res_len;

    return 0;
}

int simulated_annealing(Section *results, size_t res_len, Room *rooms, size_t rm_len, Section **ret, size_t *ret_len)
{
    double temperature = 5000000;
    const double COOLING_RATE = 0.00002;
    const double COOLING_MUL = 1 - COOLING_RATE;
    size_t e = energy2(results, res_len, rooms, rm_len);

    while (temperature > 1)
    {
        Section *nxt;
        size_t nxt_len;
        Section *tmp = (Section *)malloc(sizeof(Section) * res_len);
        if (tmp == NULL)
            return 2;
        for (size_t i = 0; i < res_len; i++)
        {
            tmp[i].staffs = allocate_matrix(results[i].len, 13);
            for (size_t j = 0; j < results[i].len; j++)
            {
                memcpy(tmp[i].staffs[j], results[i].staffs[j], sizeof(int) * 13);
            }
            tmp[i].len = results[i].len;
        }

        int r = neighbor(tmp, res_len, &nxt, &nxt_len);
        if (r != 0)
            return r;
        size_t ep = energy2(nxt, nxt_len, rooms, rm_len);

        double p = exp(((double)(ep - e)) / temperature);

        if (ep < e || (((double)(rand() % 100)) / 100) < p)
        {
            for (size_t i = 0; i < res_len; i++)
            {
                free_matrix(results[i].staffs, results[i].len);
            }
            free(results);
            results = tmp;
            e = ep;
        }
        else
        {
            for (size_t i = 0; i < res_len; i++)
            {
                free_matrix(tmp[i].staffs, tmp[i].len);
            }
            free(tmp);
        }

        temperature *= COOLING_MUL;
    }

    *ret = results;
    *ret_len = res_len;
    return 0;
}

int main()
{
    srand(time(NULL));

    size_t n = 13, r = 6;
    Room *rooms = gen_rooms(r, n);
    size_t t = 6;

    Section *result = solve(rooms, r, t, n);

    Section *ans;
    size_t ans_len;
    int sim_result = simulated_annealing(result, t, rooms, r, &ans, &ans_len);
    if (sim_result != 0)
        exit(sim_result);

    for (size_t i = 0; i < t; i++)
    {
        for (size_t j = 0; j < ans[i].len; j++)
        {
            printf("[");
            for (size_t k = 0, s = size(ans[i].staffs[j]); k < s; k++)
            {
                printf("%d", ans[i].staffs[j][k]);
                if (k != s - 1)
                    printf(" ");
            }

            printf("] ");
        }
        printf("\n");
    }

    return 0;
}
