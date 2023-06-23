// some codes are copied from https://github.com/Z3Prover/z3/blob/master/examples/c/test_capi.c

#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <memory.h>
#include <setjmp.h>
#include <z3.h>

// #define LOG_Z3_CALLS

#ifdef LOG_Z3_CALLS
#define LOG_MSG(msg) Z3_append_log(msg)
#else
#define LOG_MSG(msg) ((void)0)
#endif

/**
   \defgroup capi_ex C API examples
*/
/**@{*/
/**
   @name Auxiliary Functions
*/
/**@{*/

/**
   \brief exit gracefully in case of error.
*/
void exitf(const char *message)
{
    fprintf(stderr, "BUG: %s.\n", message);
    exit(1);
}

/**
   \brief exit if unreachable code was reached.
*/
void unreachable()
{
    exitf("unreachable code was reached");
}

/**
   \brief Simpler error handler.
 */
void error_handler(Z3_context c, Z3_error_code e)
{
    printf("Error code: %d\n", e);
    printf("Detail: %s\n", Z3_get_error_msg(c, e));
    exitf("incorrect use of Z3");
}

static jmp_buf g_catch_buffer;
/**
   \brief Low tech exceptions.

   In high-level programming languages, an error handler can throw an exception.
*/
void throw_z3_error(Z3_context c, Z3_error_code e)
{
    longjmp(g_catch_buffer, e);
}

/**
   \brief Error handling that depends on checking an error code on the context.

*/

void nothrow_z3_error(Z3_context c, Z3_error_code e)
{
    // no-op
}

/**
   \brief Create a logical context.

   Enable model construction. Other configuration parameters can be passed in the cfg variable.

   Also enable tracing to stderr and register custom error handler.
*/
Z3_context mk_context_custom(Z3_config cfg, Z3_error_handler err)
{
    Z3_context ctx;

    Z3_set_param_value(cfg, "model", "true");
    ctx = Z3_mk_context(cfg);
    Z3_set_error_handler(ctx, err);

    return ctx;
}

Z3_solver mk_solver(Z3_context ctx)
{
    Z3_solver s = Z3_mk_solver(ctx);
    Z3_solver_inc_ref(ctx, s);
    return s;
}

void del_solver(Z3_context ctx, Z3_solver s)
{
    Z3_solver_dec_ref(ctx, s);
}

/**
   \brief Create a logical context.

   Enable model construction only.

   Also enable tracing to stderr and register standard error handler.
*/
Z3_context mk_context()
{
    Z3_config cfg;
    Z3_context ctx;
    cfg = Z3_mk_config();
    ctx = mk_context_custom(cfg, error_handler);
    Z3_del_config(cfg);
    return ctx;
}

/**
   \brief Create a logical context.

   Enable fine-grained proof construction.
   Enable model construction.

   Also enable tracing to stderr and register standard error handler.
*/
Z3_context mk_proof_context()
{
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx;
    Z3_set_param_value(cfg, "proof", "true");
    ctx = mk_context_custom(cfg, throw_z3_error);
    Z3_del_config(cfg);
    return ctx;
}

/**
   \brief Create a variable using the given name and type.
*/
Z3_ast mk_var(Z3_context ctx, const char *name, Z3_sort ty)
{
    Z3_symbol s = Z3_mk_string_symbol(ctx, name);
    return Z3_mk_const(ctx, s, ty);
}

typedef struct _schedule_input_
{
    size_t row;
    size_t *cols_x, *cols_y;
    size_t cols_len;
    size_t n_people;
    int max_co_assign;
} schedule_input;

typedef struct _schedule_entry_
{
    size_t row;
    size_t col;
    char *name;
} schedule_entry;

int schedule(const schedule_input input)
{
    Z3_context ctx = mk_context();
    Z3_solver solver = mk_solver(ctx);
    Z3_sort int_sort, array_sort, mat_sort, mat3_sort;
    Z3_ast ms;

    char **names = (char **)malloc(sizeof(char *) * input.n_people);
    if (names == NULL)
        return 1;
    for (size_t i = 0; i < input.n_people; i++)
    {
        names[i] = (char *)malloc(sizeof(char) * 24);
        sprintf(names[i], "P%ld", i);
    }

    int_sort = Z3_mk_int_sort(ctx);
    array_sort = Z3_mk_array_sort(ctx, int_sort, int_sort);
    mat_sort = Z3_mk_array_sort(ctx, int_sort, array_sort);
    mat3_sort = Z3_mk_array_sort(ctx, int_sort, mat_sort);
    ms = mk_var(ctx, "m", mat3_sort);

    Z3_ast *int_row = (Z3_ast *)malloc(sizeof(Z3_ast) * sizeof(input.cols_len));
    if (int_row == NULL)
        return 1;
    Z3_ast *int_col = (Z3_ast *)malloc(sizeof(Z3_ast) * sizeof(input.row));
    if (int_col == NULL)
        return 1;

    // for each people
    for (size_t i = 0; i < input.n_people; i++)
    {
        Z3_ast m = Z3_mk_select(ctx, ms, Z3_mk_int64(ctx, i, int_sort));
        for (size_t r = 0; r < input.row; r++)
        {
            Z3_ast row = Z3_mk_select(ctx, m, Z3_mk_int64(ctx, r, int_sort));
            for (size_t c = 0; c < input.cols_len; c++)
            {
                int_row[c] = Z3_mk_select(ctx, row, Z3_mk_int64(ctx, c, int_sort));
            }
            Z3_ast row_sum = Z3_mk_add(ctx, input.cols_len, int_row);
            Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, row_sum, Z3_mk_int64(ctx, 1, int_sort)));
        }

        for (size_t c = 0; c < input.cols_len; c++)
        {
            for (size_t r = 0; r < input.row; r++)
            {
                Z3_ast row = Z3_mk_select(ctx, m, Z3_mk_int64(ctx, r, int_sort));
                int_col[r] = Z3_mk_select(ctx, row, Z3_mk_int64(ctx, c, int_sort));
            }
            Z3_ast col_sum = Z3_mk_add(ctx, input.row, int_col);
            Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, col_sum, Z3_mk_int64(ctx, 1, int_sort)));
        }

        for (size_t r = 0; r < input.row; r++)
        {
            Z3_ast row = Z3_mk_select(ctx, m, Z3_mk_int64(ctx, r, int_sort));
            for (size_t c = 0; c < input.cols_len; c++)
            {
                Z3_ast v = Z3_mk_select(ctx, row, Z3_mk_int64(ctx, c, int_sort));
                Z3_solver_assert(ctx, solver, Z3_mk_ge(ctx, v, Z3_mk_int64(ctx, 0, int_sort)));
            }
        }
    }

    if (input.max_co_assign > 0)
    {
        Z3_ast *conds = (Z3_ast *)malloc(sizeof(Z3_ast) * (input.row * input.cols_len));
        if (conds == NULL)
            return 1;
        int *coeffs = (int *)malloc(sizeof(int) * (input.row * input.cols_len));
        if (coeffs == NULL)
            return 1;

        for (size_t i = 0, n = input.row * input.cols_len; i < n; i++)
        {
            coeffs[i] = 1;
        }

        for (size_t i = 0; i < input.n_people; i++)
        {
            Z3_ast ma = Z3_mk_select(ctx, ms, Z3_mk_int64(ctx, i, int_sort));
            for (size_t j = i + 1; j < input.n_people; j++)
            {
                Z3_ast mb = Z3_mk_select(ctx, ms, Z3_mk_int64(ctx, j, int_sort));
                Z3_ast *cond_it = conds;

                for (size_t r = 0; r < input.row; r++)
                {
                    Z3_ast ma_row = Z3_mk_select(ctx, ma, Z3_mk_int64(ctx, r, int_sort));
                    Z3_ast mb_row = Z3_mk_select(ctx, mb, Z3_mk_int64(ctx, r, int_sort));
                    for (size_t c = 0; c < input.cols_len; c++)
                    {
                        Z3_ast l_gt_zero = Z3_mk_gt(
                            ctx,
                            Z3_mk_select(ctx, ma_row, Z3_mk_int64(ctx, c, int_sort)),
                            Z3_mk_int64(ctx, 0, int_sort));
                        Z3_ast r_gt_zero = Z3_mk_gt(
                            ctx,
                            Z3_mk_select(ctx, mb_row, Z3_mk_int64(ctx, c, int_sort)),
                            Z3_mk_int64(ctx, 0, int_sort));
                        Z3_ast args[] = {l_gt_zero, r_gt_zero};
                        *cond_it = Z3_mk_and(ctx, 2, args);
                        cond_it++;
                    }
                }

                Z3_solver_assert(
                    ctx,
                    solver,
                    Z3_mk_pble(ctx, input.row * input.cols_len, conds, coeffs, input.max_co_assign));
            }
        }

        free(conds);
        free(coeffs);
    }

    Z3_ast *assigns = (Z3_ast *)malloc(sizeof(Z3_ast) * input.n_people);
    if (assigns == NULL)
        return 1;

    for (size_t r = 0; r < input.row; r++)
    {
        for (size_t c = 0; c < input.cols_len; c++)
        {
            for (size_t i = 0; i < input.n_people; i++)
            {
                Z3_ast m = Z3_mk_select(ctx, ms, Z3_mk_int64(ctx, i, int_sort));
                Z3_ast row = Z3_mk_select(ctx, m, Z3_mk_int64(ctx, r, int_sort));
                Z3_ast assign = Z3_mk_select(ctx, row, Z3_mk_int64(ctx, c, int_sort));
                assigns[i] = assign;
            }
            Z3_ast assign_total = Z3_mk_add(ctx, input.n_people, assigns);

            size_t x = input.cols_x[c];
            size_t y = input.cols_y[c];
            if (x == y)
            {
                Z3_solver_assert(ctx, solver, Z3_mk_eq(ctx, assign_total, Z3_mk_int64(ctx, x, int_sort)));
            }
            else
            {
                Z3_ast ge_mn = Z3_mk_ge(
                    ctx,
                    assign_total,
                    Z3_mk_int64(ctx, x, int_sort));
                Z3_ast le_mx = Z3_mk_le(
                    ctx,
                    assign_total,
                    Z3_mk_int64(ctx, y, int_sort));
                Z3_ast args[] = {ge_mn, le_mx};
                Z3_solver_assert(
                    ctx,
                    solver,
                    Z3_mk_and(ctx, 2, args));
            }
        }
    }

    Z3_lbool res = Z3_solver_check(ctx, solver);
    if (res != Z3_L_TRUE)
    {
        printf("unsat\n");
    }
    else
    {
        Z3_model model = Z3_solver_get_model(ctx, solver);
        schedule_entry *entries = (schedule_entry *)malloc(sizeof(schedule_entry) * (input.row * input.cols_len * input.n_people));
        if (entries == NULL)
            return 1;
        size_t entry_cnt = 0;
        for (size_t i = 0; i < input.n_people; i++)
        {
            Z3_ast m = Z3_mk_select(ctx, ms, Z3_mk_int64(ctx, i, int_sort));
            for (size_t r = 0; r < input.row; r++)
            {
                Z3_ast row = Z3_mk_select(ctx, m, Z3_mk_int64(ctx, r, int_sort));
                for (size_t c = 0; c < input.cols_len; c++)
                {
                    Z3_ast assign = Z3_mk_select(ctx, row, Z3_mk_int64(ctx, c, int_sort));
                    Z3_ast out;
                    Z3_lbool success = Z3_model_eval(ctx, model, assign, true, &out);
                    if (success != Z3_L_TRUE)
                        return 2;
                    int outi = -1;
                    if (Z3_get_numeral_int(ctx, out, &outi))
                    {
                        if (outi > 0)
                        {
                            entries[entry_cnt].row = r;
                            entries[entry_cnt].col = c;
                            entries[entry_cnt].name = names[i];
                            entry_cnt++;
                        }
                    }
                    else
                    {
                        return 3;
                    }
                }
            }
        }

        for (size_t r = 0; r < input.row; r++)
        {
            for (size_t c = 0; c < input.cols_len; c++)
            {
                printf("[");
                int first = 1;
                for (size_t i = 0; i < entry_cnt; i++)
                {
                    if (entries[i].row == r && entries[i].col == c)
                    {
                        if (first)
                        {
                            first = 0;
                        }
                        else
                        {
                            printf(" ");
                        }
                        printf("%s", entries[i].name);
                    }
                }
                printf("] ");
            }
            printf("\n");
        }

        free(entries);
    }

    free(assigns);
    free(int_row);
    free(int_col);
    free(names);
    return 0;
}

int main()
{
#ifdef LOG_Z3_CALLS
    Z3_open_log("z3.log");
#endif

    size_t xs[] = {3, 3, 3, 3, 3};
    size_t ys[] = {4, 4, 4, 4, 4};

    schedule_input input;
    input.row = 5;
    input.cols_len = 5;
    input.cols_x = (size_t *)malloc(sizeof(size_t) * 5);
    if (input.cols_x == NULL)
        return 1;
    input.cols_y = (size_t *)malloc(sizeof(size_t) * 5);
    if (input.cols_y == NULL)
        return 1;
    for (size_t i = 0; i < input.cols_len; i++)
    {
        input.cols_x[i] = xs[i];
        input.cols_y[i] = ys[i];
    }
    input.n_people = 16;
    input.max_co_assign = 3;
    schedule(input);

    return 0;
}
