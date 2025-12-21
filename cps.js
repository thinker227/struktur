function run(x) {
    while (x && x.func) {
        x = x.res ??= x.func.apply(null, x.args);
        // x = x.func.apply(null, x.args);
    }
}

function thunk(func, ...args) {
    return { func, args, res: undefined }
}

/*
let fib = fun n ->
          if n <= 1
          then n
          else fib (n - 1) + fib (n - 2)
*/

function fib(n, cont) {
    if (n <= 1) {
        return thunk(cont,
            n
        );
    } else {
        return thunk(fib,
            /* n: */
            n - 1,
            /* cont: */
            x => thunk(fib,
                /* n: */
                n - 2,
                /* cont: */
                y => thunk(cont,
                    x + y
                )
            )
        );
    }
}

run(fib(30, console.log));
