function run(x) {
    while (x && x.func) {
        x = x.func.apply(null, x.args);
    }

    return x;
}

function thunk(func, ...args) {
    return { func, args };
}

