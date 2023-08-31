add_cus_dep('lagda', 'tex', 0, 'lagda');
sub lagda  {   system( "agda --latex --latex-dir=.  \"$_[0].lagda\" "); }
