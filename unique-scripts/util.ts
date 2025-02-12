export function requireExactlyOne(args: any, required: string[]) {
    const supplied = requireAtLeastOne(args, required);

    if (supplied.length > 1) {
        console.error(
            'Conflicting options:',
            supplied.map(o => '--' + o).join(', ')
        );
        process.exit(-1);
    }
}

export function requireAtLeastOne(args: any, required: string[]) {
    const requiredSupplied = required.filter(r => args[r] !== undefined);

    if (requiredSupplied.length === 0) {
        console.error(
            'One of the following options *must* be provided:',
            required.map(o => '--' + o).join(', ')
        );
        process.exit(-1);
    }

    return requiredSupplied;
}
