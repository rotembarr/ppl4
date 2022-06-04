export const MISSING_KEY = '___MISSING_KEY___'
export const MISSING_TABLE_SERVICE = '___MISSING_TABLE_SERVICE___'

export type Table<T> = Readonly<Record<string, Readonly<T>>>
export type mutableTable<T> = Record<string, Readonly<T>>

export type TableService<T> = {
    get(key: string): Promise<T>;
    set(key: string, val: T): Promise<void>;
    delete(key: string): Promise<void>;
}

function toMutableTable<T>(table: Table<T>): mutableTable<T> {
    let out = {};
    Object.assign(out, table);
    return out;
}
function errorPromise<T>(): Promise<T> {
    return new Promise(
        function (resolve, reject) {
            reject(MISSING_KEY);
        }
    );
}
function voidPromise(): Promise<void> {
    return new Promise(
        function (resolve, reject) {
            resolve();
        }
    );
}

function str(s: string): string {return s};
// Q 2.1 (a)
export function makeTableService<T>(sync: (table?: Table<T>) => Promise<Table<T>>): TableService<T> {
    // optional initialization code
    let _sync : ((table?: Table<T>) => Promise<Table<T>>) = sync;

    return {
        get(key: string): Promise<T> {
            return _sync()
            .then((table) => 
                new Promise (
                    function (resolve, reject) {
                        for (const [k, v] of Object.entries(table)) {
                            if (key === k) {
                                resolve(v);
                            }
                        }
                        reject(MISSING_KEY);
                    }
                )
            )
        },
        set(key: string, val: T): Promise<void> {
            return _sync()
            .then((table: Table<T>) => {
                const newTable = Object.assign(toMutableTable(table), {[key]: val});
                return _sync(newTable)
            })
            .then((updatedPromise: Table<T>) => {
                voidPromise()
            })

        },
        delete(key: string): Promise<void> {
            return _sync()
            .then((table: Table<T>) => 
                new Promise<Table<T>>(
                    function (resolve, reject) {
                        // Check if key exists
                        !Object.keys(table).includes(key) ?
                            reject(MISSING_KEY) :
                            resolve ( Object.entries(table).reduce(
                                (acc, [k, v]) => (key === k) ? acc :(Object.assign(acc, {[k]: v})), {}))
                    }
                )
            )
            .then((newTable: Table<T>) => _sync(newTable))
            .then((updatedPromise: Table<T>) => 
                voidPromise()
            )
        }
    }
}

// Q 2.1 (b)
export function getAll<T>(store: TableService<T>, keys: string[]): Promise<T[]> {
    return Promise.all(keys.map((key) => store.get(key)))
}


// Q 2.2
export type Reference = { table: string, key: string }

export type TableServiceTable = Table<TableService<object>>

export function isReference<T>(obj: T | Reference): obj is Reference {
    return typeof obj === 'object' && 'table' in obj
}

export async function constructObjectFromTables(tables: TableServiceTable, ref: Reference) {

    // Fetch ref.table from tables.
    if (!Object.keys(tables).includes(ref.table)) {
        return Promise.reject(MISSING_TABLE_SERVICE);
    } 
    const table = tables[ref.table]
    
    // find ref.key in the table we have got.
    let val = await table.get(ref.key);

    // Recursively change all the reference values in the record we found to thier true value
    if (typeof val === 'object') {
        for (const [k, v] of Object.entries(val)) {
            if (isReference(v)) {
                Object.assign(val, {[k]: await constructObjectFromTables(tables, v)});
            } 
        }
    }

    return val

}

// Q 2.3

export function lazyProduct<T1, T2>(g1: () => Generator<T1>, g2: () => Generator<T2>): () => Generator<[T1, T2]> {
    return function* () {
        for (let d1 of g1()) {
            for (let d2 of g2()) {
                yield [d1, d2];
            }
        }
    }
}

export function lazyZip<T1, T2>(g1: () => Generator<T1>, g2: () => Generator<T2>): () => Generator<[T1, T2]> {
    return function* () {
        const d1 = g1();
        const d2 = g2();
        let d11 = d1.next();
        while(d11.done === false) {
            yield [d11.value, d2.next().value];
            d11 = d1.next();
        }
    }
}

// Q 2.4
export type ReactiveTableService<T> = {
    get(key: string): T;
    set(key: string, val: T): Promise<void>;
    delete(key: string): Promise<void>;
    subscribe(observer: (table: Table<T>) => void): void
}

export async function makeReactiveTableService<T>(sync: (table?: Table<T>) => Promise<Table<T>>, optimistic: boolean): Promise<ReactiveTableService<T>> {

    // Variables.
    let _sync: ((table?: Table<T>) => Promise<Table<T>>) = sync;
    let _optimistic: boolean = optimistic
    let _table: Table<T> = await sync()
    let _observer: ((table: Table<T>) => void) = null as any;

    const handleMutation = async (newTable: Table<T>) => {
        if ((_observer != null) && (_optimistic)) {
            _observer(_table)
        }

        _table = await _sync(newTable)

        if (!(_observer === null)) {
            _observer(_table)
        }
    }

    return {
        get(key: string): T {
            if (key in _table) {
                return _table[key]
            } else {
                throw MISSING_KEY
            }
        },
        set(key: string, val: T): Promise<void> {
            return handleMutation(Object.assign(_table, {[key]: val}))
        },
        delete(key: string): Promise<void> {
            if (!Object.keys(_table).includes(key)) {
                throw MISSING_KEY;
            } else {
                return handleMutation(
                    ( Object.entries(_table).reduce(
                        (acc, [k, v]) => (key === k) ? acc :(Object.assign(acc, {[k]: v})), {}))
                )
            }
        },
        subscribe(observer: (table: Table<T>) => void): void {
            _observer = observer
        }
    }
}