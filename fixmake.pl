#!/usr/bin/env perl

while (<>) {
    s#./-dont-load-proofs#./.#g;
    s#cd \./\. ; \$\(MAKE\) all#cd ./. ; echo \$\(MAKE\) all#;
    s#cd \./\. ; \$\(MAKE\) clean#cd ./. ; echo \$\(MAKE\) clean#;
    s#cd \./\. && \$\(MAKE\) clean#cd ./. ; echo \$\(MAKE\) clean#;
    s#cd "./." && \$\(MAKE\) all#cd ./. ; echo \$\(MAKE\) all#;
    print;
}
