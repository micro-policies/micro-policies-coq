If you're having trouble installing the `text-icu` dependency on Mac OS X, I
(Antal) found the following successful:

1.  Install `icu4c` from [homebrew](http://brew.sh/), if you haven't already:
    
        brew info icu4c
    
    will check to see if `icu4c` is installed ("Built from source" or "Poured
    from bottle" lines indicate that it is; a "Not installed" line indicates
    that it's not); if necessary, then
    
        brew install icu4c

    will install `icu4c`.

2. Install `text-icu` while looking for those files:

        DYLD_LIBRARY_PATH=/usr/local/opt/icu4c/lib cabal install text-icu --extra-include-dirs=/usr/local/opt/icu4c/include --extra-lib-dirs=/usr/local/opt/icu4c/lib

Your mileage with these instructions may vary, so feel free to edit this file or
create an appropriate new one if you solve this (or another) problem in a
different way!
