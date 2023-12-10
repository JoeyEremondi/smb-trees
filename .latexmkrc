add_cus_dep('lagda', 'tex', 0, 'lagda');
sub lagda  {   system( "agda --latex --latex-dir=. --only-scope-checking  \"$_[0].lagda\" "); }
$pdflatex=q/xelatex -synctex=1 %O %S/
