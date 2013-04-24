#!/bin/sh
# Script to convert .fat file to .ats files
# Date: April 2013
# Author: heizmann@informatik.uni-freiburg.de

# perl -i -pe "s/'/\\\'/" $1
perl -i -pe "s/\ :=\ /\ =\ /g" $1
# perl -i -pe "s/\"/\'/" $1
perl -i -pe "s/#nwa/NestedWordAutomaton/" $1
perl -i -pe "s/#callAlphabet/callAlphabet/" $1
perl -i -pe "s/#internalAlphabet/internalAlphabet/" $1
perl -i -pe "s/#returnAlphabet/returnAlphabet/" $1
perl -i -pe "s/#states/states/" $1
perl -i -pe "s/#initialStates/initialStates/" $1
perl -i -pe "s/#finalStates/finalStates/" $1
perl -i -pe "s/#callTransitions/callTransitions/" $1
perl -i -pe "s/#internalTransitions/internalTransitions/" $1
perl -i -pe "s/#returnTransitions/returnTransitions/" $1

perl -i -pe "s/#net/PetriNet/" $1
perl -i -pe "s/#alphabet/alphabet/" $1
perl -i -pe "s/#places/places/" $1
perl -i -pe "s/#transitions/transitions/" $1
perl -i -pe "s/#initialMarking/initialMarking/" $1
perl -i -pe "s/#acceptingPlaces/acceptingPlaces/" $1



perl -i -pe 's/^\)\s*$/\);\n/' $1
perl -i -pe 's/#Print ([^\r\n]*)/print\($1\);/' $1

perl -i -pe 's/#AcceptsBuchi\ ([^\[]*)\ ([^\r\n]*)/assert\(buchiAccepts\($1, $2\)\);/' $1
perl -i -pe 's/#NotAcceptsBuchi\ ([^\[]*)\ ([^\r\n]*)/assert\(!buchiAccepts\($1, $2\)\);/' $1
perl -i -pe 's/#IsNotEmptyBuchi\ *([^\r\n]*)/assert\(!buchiIsEmpty\($1\)\);/' $1
perl -i -pe 's/#IsEmptyBuchi\ *([^\r\n]*)/assert\(buchiIsEmpty\($1\)\);/' $1

perl -i -pe 's/#Accepts\ ([^\\[]*)\ ([^\r\n]*)/assert\(accepts\($1, $2\)\);/' $1
perl -i -pe 's/#NotAccepts\ ([^\[]*)\ ([^\r\n]*)/assert\(!accepts\($1, $2\)\);/' $1
perl -i -pe 's/#IsNotEmpty\ *([^\r\n]*)/assert\(!isEmpty\($1\)\);/' $1
perl -i -pe 's/#IsEmpty\ *([^\r\n]*)/assert\(isEmpty\($1\)\);/' $1