# toy

## Building and running

You'll need Idris to run most of this.

### OS X caveats

If z3 isn't installed in a location like `/usr` or `/usr/local`, then `stack`/`cabal` will have trouble finding it.
To fix, assuming it's in `/Users/foo/local`:

1. Add these into your `~/.stack/config.yaml`:
```yaml
extra-include-dirs:
- /Users/foo/local/include
extra-lib-dirs:
- /Users/foo/local/lib
```

2. Symlink the library into a standard path: `sudo ln -s ~/local/lib/libz3.dylib /usr/local/lib`
