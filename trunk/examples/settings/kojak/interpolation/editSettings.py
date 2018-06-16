import os

def writeSettingsFile(path, fn) :
  fnWPath = os.path.join(path, fn)
  #print('writing to file: ', fnWPath)
  print(fnWPath)
  f = open(fnWPath, 'w')

  #common -- BlockEncoding
  print(standards_for_all, file=f)
  #print("", file=f)

  #RCFGBuilder
  if bitvectorKey in fn:
   print(rcfgBuilder_bv, file=f)
  elif floatKey in fn:
   print(rcfgBuilder_float, file=f)
  elif intKey in fn:
   print(rcfgBuilder_nonbv, file=f)
  else:
   print('ERROR: neither Integer nor Bitvector nor Float in filename')

  #C translation 
  if reachKey in fn and bitvectorKey in fn:
    print(cacsl_reach_bv, file=f)
  elif reachKey in fn and floatKey in fn:
    print(cacsl_reach_float, file=f)
  elif reachKey in fn and intKey in fn:
    print(cacsl_reach_nonbv, file=f)
  elif memsafetyKey in fn and intKey in fn:
    print(cacsl_memsafety_nonbv, file=f)
  else:
   print('ERROR: did not recognize translation mode')

  #codecheck and Automizer settings

  kojakString = ''
  automizerString = ''

  kojakString += dateline + '\n'
  kojakString += codecheckCommon + '\n'

  #automizerString += dateline, file=f)
  automizerString += automizerCommon + '\n'

  if treeinterpolationKey in fn:
   kojakString += treeItpKojak + '\n'
   automizerString += treeItpAutomizer + '\n'
  elif nestedinterpolationKey in fn:
   kojakString += nestedItpKojak + '\n'
   automizerString += nestedItpAutomizer + '\n'
  elif fpKey in fn:
   kojakString += fpItpKojak + '\n'
   automizerString += fpItpAutomizer + '\n'
  elif bpKey in fn:
   kojakString += bpItpKojak + '\n'
   automizerString += bpItpAutomizer + '\n'
  else:
   print('ERROR: did not recognize interpolation mode')

  if solverSMTInterpolKey in fn and treeinterpolationKey in fn:
   kojakString += solverCallSMTInterpolKojakInt + '\n'
   kojakString += interpolationModeSMTInterpolKojak + '\n'
   automizerString += solverCallSMTInterpolAutomizerInt + '\n'
   automizerString += interpolationModeSMTInterpolAutomizer + '\n'
  elif solverSMTInterpolKey in fn and (fpKey in fn or bpKey in fn):
   kojakString += solverCallSMTInterpolKojakInt + '\n'
   kojakString += interpolationModeTraceInterpolationKojak + '\n'
   automizerString += solverCallSMTInterpolAutomizerInt + '\n'
   automizerString += interpolationModeTraceInterpolationAutomizer + '\n'
  elif solverZ3Key in fn and nestedinterpolationKey in fn and intKey in fn:
   kojakString += solverCallZ3KojakInt + '\n'
   kojakString += interpolationModeZ3Kojak + '\n'
   automizerString += solverCallZ3AutomizerInt + '\n'
   automizerString += interpolationModeZ3Automizer + '\n'
  elif solverZ3Key in fn and nestedinterpolationKey in fn and bitvectorKey in fn:
   kojakString += solverCallZ3KojakBitvector + '\n'
   kojakString += interpolationModeZ3Kojak + '\n'
   automizerString += solverCallZ3AutomizerBitvector + '\n'
   automizerString += interpolationModeZ3Automizer + '\n'
  elif solverZ3Key in fn and (fpKey in fn or bpKey in fn) and intKey in fn:
   kojakString += solverCallZ3KojakInt + '\n'
   kojakString += interpolationModeTraceInterpolationKojak + '\n'
   automizerString += solverCallZ3AutomizerInt + '\n'
   automizerString += interpolationModeTraceInterpolationAutomizer + '\n'
  elif solverZ3Key in fn and (fpKey in fn or bpKey in fn) and bitvectorKey in fn:
   kojakString += solverCallZ3KojakBitvector + '\n'
   kojakString += interpolationModeTraceInterpolationKojak + '\n'
   automizerString += solverCallZ3AutomizerBitvector + '\n'
   automizerString += interpolationModeTraceInterpolationAutomizer + '\n'
  elif solverZ3Key in fn and floatKey in fn:
   kojakString += solverCallZ3KojakFloat + '\n'
   kojakString += interpolationModeTraceInterpolationKojak + '\n'
   automizerString += solverCallZ3AutomizerFloat + '\n'
   automizerString += interpolationModeTraceInterpolationAutomizer + '\n'
  elif solverPrincessKey in fn:
   kojakString += solverCallPrincessKojakInt + '\n'
   kojakString += interpolationModePrincessKojak + '\n'
   automizerString += solverCallPrincessAutomizerInt + '\n'
   automizerString += interpolationModePrincessAutomizer + '\n'
  elif solverCVC4Key in fn and intKey in fn:
   kojakString += solverCallCVC4KojakInt + '\n'
   kojakString += interpolationModeTraceInterpolationKojak + '\n'
   automizerString += solverCallCVC4AutomizerInt + '\n'
   automizerString += interpolationModeTraceInterpolationAutomizer + '\n'
  elif solverCVC4Key in fn and bitvectorKey in fn:
   kojakString += solverCallCVC4KojakBitvector + '\n'
   kojakString += interpolationModeTraceInterpolationKojak + '\n'
   automizerString += solverCallCVC4AutomizerBitvector + '\n'
   automizerString += interpolationModeTraceInterpolationAutomizer + '\n'
  elif solverMathSATKey in fn and intKey in fn:
   kojakString += solverCallMathSATKojakInt + '\n'
   kojakString += interpolationModeTraceInterpolationKojak + '\n'
   automizerString += solverCallMathSATAutomizerInt + '\n'
   automizerString += interpolationModeTraceInterpolationAutomizer + '\n'
  elif solverMathSATKey in fn and bitvectorKey in fn:
   kojakString += solverCallMathSATKojakBitvector + '\n'
   kojakString += interpolationModeTraceInterpolationKojak + '\n'
   automizerString += solverCallMathSATAutomizerBitvector + '\n'
   automizerString += interpolationModeTraceInterpolationAutomizer + '\n'
  elif solverMathSATKey in fn and floatKey in fn:
   kojakString += solverCallMathSATKojakFloat + '\n'
   kojakString += interpolationModeTraceInterpolationKojak + '\n'
   automizerString += solverCallMathSATAutomizerFloat + '\n'
   automizerString += interpolationModeTraceInterpolationAutomizer + '\n'
  else:
   print('ERROR: did not recognize solver to use: ' + fn)

  if lvOnKey not in fn:
   kojakString += dontUseLVKojak + '\n'
   automizerString += dontUseLVAutomizer + '\n'
  elif lvOnKey in fn:
   kojakString += useLVKojak + '\n'
   automizerString += useLVAutomizer + '\n'

  if ucOnKey not in fn:
   kojakString += dontUseUCKojak + '\n'
   automizerString += dontUseUCAutomizer + '\n'
  #elif ucOnKey in fn:
   #kojakString += useUCKojak, file=f)

  if kojakKey in fn:
   kojakString += useKojakAlgorithm + '\n'
  elif impulseKey in fn:
   kojakString += useImpulseAlgorithm + '\n'

  print(kojakString, file=f)
  print(automizerString, file=f)

#############################################################################
#######  the contents of the settings files are hardcoded in this section ###
#############################################################################

standards_for_all = '''
#Sat Nov 14 10:48:36 CET 2015
\!/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.blockencoding=
file_export_version=3.0
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.blockencoding/Rating-Boundary\ (empty\ for\ LBE)=4
@de.uni_freiburg.informatik.ultimate.plugins.generator.blockencoding=0.0.1
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.blockencoding/Strategy\ for\ the\ edge\ rating=DISJUNCTIVE_RATING

#Thu Oct 29 23:01:13 CET 2015
file_export_version=3.0
@de.uni_freiburg.informatik.ultimate.boogie.procedureinliner=0.0.1
\!/instance/de.uni_freiburg.informatik.ultimate.boogie.procedureinliner=
/instance/de.uni_freiburg.informatik.ultimate.boogie.procedureinliner/to\ procedures,\ called\ more\ than\ once=true'''


####### RCFGBuilder settings #########

rcfgBuilder_bv = '''#Fri Oct 24 16:34:36 CEST 2014
\!/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder=
file_export_version=3.0
@de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder=0.0.1
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Convert\ code\ blocks\ to\ CNF=false
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Size\ of\ a\ code\ block=SequenceOfStatements
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Command\ for\ external\ solver=z3 SMTLIB2_COMPLIANT\=true -memory\:2024 -smt2 -in -t\:2000
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Logic\ for\ external\ solver=AUFBV
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Dump\ SMT\ script\ to\ file=false
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/To\ the\ following\ directory=./dump/ '''

rcfgBuilder_float = '''#Fri Oct 24 16:34:36 CEST 2014
\!/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder=
file_export_version=3.0
@de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder=0.0.1
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Convert\ code\ blocks\ to\ CNF=false
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Size\ of\ a\ code\ block=SequenceOfStatements
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Command\ for\ external\ solver=z3 SMTLIB2_COMPLIANT\=true -memory\:2024 -smt2 -in -t\:12000
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Logic\ for\ external\ solver=ALL
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Dump\ SMT\ script\ to\ file=false
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/To\ the\ following\ directory=./dump/ '''



rcfgBuilder_nonbv = '''#Fri Oct 24 16:34:36 CEST 2014
\!/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder=
file_export_version=3.0
@de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder=0.0.1
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Convert\ code\ blocks\ to\ CNF=false
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Size\ of\ a\ code\ block=SequenceOfStatements
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Command\ for\ external\ solver=z3 SMTLIB2_COMPLIANT\=true -memory\:2024 -smt2 -in -t\:2000
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Dump\ SMT\ script\ to\ file=false
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/To\ the\ following\ directory=./dump/ '''

##### C to Boogie translation settings #########

cacsl_memsafety_nonbv = '''#Fri Oct 24 16:34:36 CEST 2014
\!/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator=
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Translation\ Mode\:=SV_COMP14
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Checked\ method.\ Library\ mode\ if\ empty.=main
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/sizeof\ long=4
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/sizeof\ POINTER=4
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/sizeof\ long\ double=12
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Check\ division\ by\ zero=IGNORE
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Check\ for\ the\ main\ procedure\ if\ all\ allocated\ memory\ was\ freed=true
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/If\ two\ pointers\ are\ subtracted\ or\ compared\ they\ have\ the\ same\ base\ address=IGNORE
@de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator=0.0.1 '''

cacsl_reach_bv = '''#Fri Oct 24 16:34:36 CEST 2014
\!/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator=
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Translation\ Mode\:=SV_COMP14
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Checked\ method.\ Library\ mode\ if\ empty.=main
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/sizeof\ long=4
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/sizeof\ POINTER=4
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/sizeof\ long\ double=12
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Check\ division\ by\ zero=IGNORE
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Check\ if\ freed\ pointer\ was\ valid=false
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Pointer\ to\ allocated\ memory\ at\ dereference=IGNORE
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Check\ array\ bounds\ for\ arrays\ that\ are\ off\ heap=IGNORE
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Check\ for\ the\ main\ procedure\ if\ all\ allocated\ memory\ was\ freed=false
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/If\ two\ pointers\ are\ subtracted\ or\ compared\ they\ have\ the\ same\ base\ address=IGNORE
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Pointer\ base\ address\ is\ valid\ at\ dereference=IGNORE
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Use\ bitvectors\ instead\ of\ ints=true
@de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator=0.0.1 '''

cacsl_reach_float = '''#Fri Oct 24 16:34:36 CEST 2014
\!/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator=
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Translation\ Mode\:=SV_COMP14
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Checked\ method.\ Library\ mode\ if\ empty.=main
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/sizeof\ long=4
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/sizeof\ POINTER=4
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/sizeof\ long\ double=12
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Check\ division\ by\ zero=IGNORE
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Check\ if\ freed\ pointer\ was\ valid=false
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Pointer\ to\ allocated\ memory\ at\ dereference=IGNORE
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Check\ array\ bounds\ for\ arrays\ that\ are\ off\ heap=IGNORE
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Check\ for\ the\ main\ procedure\ if\ all\ allocated\ memory\ was\ freed=false
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/If\ two\ pointers\ are\ subtracted\ or\ compared\ they\ have\ the\ same\ base\ address=IGNORE
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Pointer\ base\ address\ is\ valid\ at\ dereference=IGNORE
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Use\ bitvectors\ instead\ of\ ints=true
@de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator=0.0.1 '''


cacsl_reach_nonbv = '''#Fri Oct 24 16:34:36 CEST 2014
\!/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator=
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Translation\ Mode\:=SV_COMP14
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Checked\ method.\ Library\ mode\ if\ empty.=main
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/sizeof\ long=4
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/sizeof\ POINTER=4
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/sizeof\ long\ double=12
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Check\ division\ by\ zero=IGNORE
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Check\ if\ freed\ pointer\ was\ valid=false
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Pointer\ to\ allocated\ memory\ at\ dereference=IGNORE
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Check\ array\ bounds\ for\ arrays\ that\ are\ off\ heap=IGNORE
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Check\ for\ the\ main\ procedure\ if\ all\ allocated\ memory\ was\ freed=false
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/If\ two\ pointers\ are\ subtracted\ or\ compared\ they\ have\ the\ same\ base\ address=IGNORE
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Pointer\ base\ address\ is\ valid\ at\ dereference=IGNORE
@de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator=0.0.1 '''

####### Kojak settings ########

dateline = '''#Wed Nov 18 19:26:57 CET 2015'''
codecheckCommon = '''@de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck=0.0.1
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Use\ standard\ solver\ (from\ RCFGBuilder)\ with\ FP\ interpolation\ as\ fallback=false
file_export_version=3.0'''

treeItpKojak = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/interpolation\ mode=Craig_TreeInterpolation'''
nestedItpKojak = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/interpolation\ mode=Craig_NestedInterpolation'''
fpItpKojak = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/interpolation\ mode=ForwardPredicates'''
bpItpKojak = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/interpolation\ mode=BackwardPredicates'''

interpolationModeTraceInterpolationKojak = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Use\ separate\ solver\ for\ tracechecks=true
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Choose\ which\ separate\ solver\ to\ use\ for\ tracechecks=External_ModelsAndUnsatCoreMode'''

interpolationModeZ3Kojak = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Use\ separate\ solver\ for\ tracechecks=true
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Choose\ which\ separate\ solver\ to\ use\ for\ tracechecks=External_Z3InterpolationMode'''

interpolationModeSMTInterpolKojak = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Use\ separate\ solver\ for\ tracechecks=true
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Choose\ which\ separate\ solver\ to\ use\ for\ tracechecks=External_SMTInterpolInterpolationMode'''

interpolationModePrincessKojak = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Use\ separate\ solver\ for\ tracechecks=true
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Choose\ which\ separate\ solver\ to\ use\ for\ tracechecks=External_PrincessInterpolationMode'''

solverCallZ3KojakInt = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Theory\ for\ external\ solver=AUFLIRA
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Command\ for\ calling\ external\ solver=z3 SMTLIB2_COMPLIANT\=true -memory\:2024 -smt2 -in'''

solverCallSMTInterpolKojakInt = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Theory\ for\ external\ solver=QF_AUFLIRA
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Command\ for\ calling\ external\ solver=smtinterpol -q'''

solverCallPrincessKojakInt = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Theory\ for\ external\ solver=AUFLIRA
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Command\ for\ calling\ external\ solver=princess +incremental +stdin'''

solverCallCVC4KojakInt = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Theory\ for\ external\ solver=AUFLIRA
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Command\ for\ calling\ external\ solver=cvc4nyu --tear-down-incremental --rewrite-divk --print-success --lang smt'''

solverCallMathSATKojakInt = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Theory\ for\ external\ solver=AUFNIRA
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Command\ for\ calling\ external\ solver=mathsat\ -unsat_core_generation=3'''

solverCallZ3KojakBitvector = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Theory\ for\ external\ solver=AUFBV
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Command\ for\ calling\ external\ solver=z3 SMTLIB2_COMPLIANT\=true -memory\:2024 -smt2 -in'''

solverCallZ3KojakFloat = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Theory\ for\ external\ solver=ALL
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Command\ for\ calling\ external\ solver=z3 SMTLIB2_COMPLIANT\=true -memory\:2024 -smt2 -in'''

solverCallCVC4KojakBitvector = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Theory\ for\ external\ solver=AUFBV
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Command\ for\ calling\ external\ solver=cvc4nyu --tear-down-incremental --rewrite-divk --print-success --lang smt'''


solverCallMathSATKojakBitvector = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Theory\ for\ external\ solver=AUFBV
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Command\ for\ calling\ external\ solver=mathsat\ -unsat_core_generation=3'''

solverCallMathSATKojakFloat = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Theory\ for\ external\ solver=QF_ABVFP
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Command\ for\ calling\ external\ solver=mathsat\ -unsat_core_generation=3'''

dontUseLVKojak = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck//Use\ live\ variables\ in\ FP/BP\ interpolation=false'''
useLVKojak = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck//Use\ live\ variables\ in\ FP/BP\ interpolation=true'''

useUCKojak = ''''''
dontUseUCKojak = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck//Use\ unsat\ cores\ in\ FP/BP\ interpolation=IGNORE'''

useKojakAlgorithm = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/the\ checking\ algorithm\ to\ use=ULTIMATE'''
useImpulseAlgorithm = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/the\ checking\ algorithm\ to\ use=IMPULSE'''


############ Automizer settings ###########

automizerCommon = '''#Thu Nov 06 16:26:23 CET 2014
\!/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction=
file_export_version=3.0
@de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction=0.0.1
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Use\ separate\ solver\ for\ trace\ checks=true'''


treeItpAutomizer = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Compute\ Interpolants\ along\ a\ Counterexample=Craig_TreeInterpolation'''
nestedItpAutomizer = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Compute\ Interpolants\ along\ a\ Counterexample=Craig_NestedInterpolation'''
fpItpAutomizer = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Compute\ Interpolants\ along\ a\ Counterexample=ForwardPredicates'''
bpItpAutomizer = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Compute\ Interpolants\ along\ a\ Counterexample=BackwardPredicates'''

dontUseLVAutomizer = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Use\ live\ variables=false'''
useLVAutomizer = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Use\ live\ variables=true'''

useUCAutomizer = ''''''
dontUseUCAutomizer = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Use\ unsat\ cores=IGNORE'''

interpolationModeTraceInterpolationAutomizer = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/SMT\ solver=External_ModelsAndUnsatCoreMode'''
interpolationModeZ3Automizer = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/SMT\ solver=External_Z3InterpolationMode'''
interpolationModePrincessAutomizer = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/SMT\ solver=External_PrincessInterpolationMode'''
interpolationModeSMTInterpolAutomizer = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/SMT\ solver=External_SMTInterpolInterpolationMode'''


solverCallMathSATAutomizerFloat = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Dump\ SMT\ script\ to\ file=false
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/To\ the\ following\ directory=./dump/
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Command\ for\ external\ solver=mathsat\ -unsat_core_generation=3
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Logic\ for\ external\ solver=QF_ABVFP'''

solverCallZ3AutomizerInt = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Dump\ SMT\ script\ to\ file=false
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/To\ the\ following\ directory=/home/matthias/ultimate/dump
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Command\ for\ external\ solver=z3 SMTLIB2_COMPLIANT\=true -memory\:2024 -smt2 -in
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Logic\ for\ external\ solver=AUFLIRA'''


solverCallSMTInterpolAutomizerInt = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Dump\ SMT\ script\ to\ file=false
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/To\ the\ following\ directory=/home/matthias/ultimate/dump
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Command\ for\ external\ solver=smtinterpol -q
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Logic\ for\ external\ solver=QF_AUFLIRA'''


solverCallPrincessAutomizerInt = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Dump\ SMT\ script\ to\ file=false
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/To\ the\ following\ directory=/home/matthias/ultimate/dump
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Command\ for\ external\ solver=princess +incremental +stdin
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Logic\ for\ external\ solver=AUFLIRA'''

solverCallCVC4AutomizerInt = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Dump\ SMT\ script\ to\ file=false
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/To\ the\ following\ directory=/home/matthias/ultimate/dump
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Command\ for\ external\ solver=cvc4nyu --tear-down-incremental --rewrite-divk --print-success --lang smt
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Logic\ for\ external\ solver=AUFLIRA'''

solverCallMathSATAutomizerInt = '''
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Dump\ SMT\ script\ to\ file=false
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/To\ the\ following\ directory=/home/matthias/ultimate/dump
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Command\ for\ external\ solver=mathsat\ -unsat_core_generation=3'''

solverCallZ3AutomizerBitvector = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Dump\ SMT\ script\ to\ file=false
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/To\ the\ following\ directory=/home/matthias/ultimate/dump
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Command\ for\ external\ solver=z3 SMTLIB2_COMPLIANT\=true -memory\:2024 -smt2 -in
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Logic\ for\ external\ solver=AUFBV'''

solverCallCVC4AutomizerBitvector = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Dump\ SMT\ script\ to\ file=false
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/To\ the\ following\ directory=/home/matthias/ultimate/dump
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Command\ for\ external\ solver=cvc4nyu --tear-down-incremental --rewrite-divk --print-success --lang smt
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Logic\ for\ external\ solver=AUFBV'''

solverCallMathSATAutomizerBitvector = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Dump\ SMT\ script\ to\ file=false
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/To\ the\ following\ directory=/home/matthias/ultimate/dump
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Command\ for\ external\ solver=mathsat\ -unsat_core_generation=3
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Logic\ for\ external\ solver=AUFBV'''

solverCallZ3AutomizerFloat = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Dump\ SMT\ script\ to\ file=false
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/To\ the\ following\ directory=./dump/
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Command\ for\ external\ solver=z3 SMTLIB2_COMPLIANT\=true -memory\:2024 -smt2 -in
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Logic\ for\ external\ solver=ALL'''


#############################################################################
#############################################################################
######## definitions of key words that make up the different settings #######
#############################################################################
#############################################################################

rootRoot = './'
bitvectorRoot = './bitvector'
floatRoot = './float'
memsafetyRoot = './memsafety'
roots = [rootRoot, bitvectorRoot, floatRoot, memsafetyRoot]

solverZ3Key = 'Z3'
solverCVC4Key = 'CVC4'
solverMathSATKey = 'Mathsat'
solverSMTInterpolKey = 'SMTInterpol'
solverPrincessKey = 'Princess'
solverKeys = [solverZ3Key, solverCVC4Key, solverMathSATKey, solverSMTInterpolKey, solverPrincessKey]
solverKeysFloat = [solverZ3Key, solverMathSATKey]
solverKeysUc = [solverZ3Key, solverCVC4Key, solverMathSATKey, solverSMTInterpolKey]
solverKeysUcBV = [solverZ3Key, solverCVC4Key, solverMathSATKey]

fpKey = 'FP'
bpKey = 'BP'
fpbpKeys = [fpKey, bpKey]

lvOnKey = 'LV'
lvOffKey = ''
lvKeys = [lvOnKey, lvOffKey]

ucOnKey = 'UC'
ucOffKey = ''
ucKeys = [ucOnKey, ucOffKey]

intKey = 'Integer'
bitvectorKey = 'Bitvector'
floatKey = 'Float'
sortKeys = [intKey, bitvectorKey, floatKey]

threeTwoBitKey = '32bit'
machineKeys = [threeTwoBitKey]

memsafetyKey = 'DerefFreeMemtrack'
reachKey = 'Reach'
translationKeys = [memsafetyKey, reachKey]

treeinterpolationKey = 'TreeInterpolation'
nestedinterpolationKey = 'NestedInterpolation'

kojakKey = 'Kojak'
impulseKey = 'Impulse'
algorithmKeys = [kojakKey, impulseKey]

#############################################################################
#############################################################################
######## fucntions to combine the different settings ############
#############################################################################
#############################################################################

def combineAll(roots, keyLists):
  sep = ''
  
  filenames = ['']
  for keyList in keyLists:
    newfilenames = []
    for fn in filenames:
      for key in keyList:
        if key is '':
          newfilenames.append(fn)
        else:
          newfilenames.append(fn + sep + key)
    filenames = newfilenames
    sep = '-'

  ending = '.epf'

  pairs = set()
  for root in roots:
    for fn in filenames:
      pairs.add((root, fn + ending))

  return pairs
    

def generateFileNames():
  fns = set()
  # trace interpolation settings
  fns |= combineAll([memsafetyRoot], [[memsafetyKey], [threeTwoBitKey], [solverZ3Key], fpbpKeys, ucKeys, lvKeys, [intKey], algorithmKeys])
  fns |= combineAll([memsafetyRoot], [[memsafetyKey], [threeTwoBitKey], solverKeysUc, [fpKey], [ucOnKey], [lvOnKey], [intKey], algorithmKeys])

  fns |= combineAll([bitvectorRoot], [[reachKey], [threeTwoBitKey], [solverZ3Key], fpbpKeys, ucKeys, lvKeys, [bitvectorKey], algorithmKeys])
  fns |= combineAll([bitvectorRoot], [[reachKey], [threeTwoBitKey], solverKeysUcBV, [fpKey], [ucOnKey], [lvOnKey], [bitvectorKey], algorithmKeys])

  fns |= combineAll([floatRoot], [[reachKey], [threeTwoBitKey], [solverZ3Key], fpbpKeys, ucKeys, lvKeys, [floatKey], algorithmKeys])
  fns |= combineAll([floatRoot], [[reachKey], [threeTwoBitKey], solverKeysFloat, [fpKey], [ucOnKey], [lvOnKey], [floatKey], algorithmKeys])

  fns |= combineAll([rootRoot], [[reachKey], [threeTwoBitKey], [solverZ3Key], fpbpKeys, ucKeys, lvKeys, [intKey], algorithmKeys])
  fns |= combineAll([rootRoot], [[reachKey], [threeTwoBitKey], solverKeysUc, [fpKey], [ucOnKey], [lvOnKey], [intKey], algorithmKeys])

  # craig interpolation settings
  fns |= combineAll([rootRoot], [[reachKey], [threeTwoBitKey], [solverZ3Key], [nestedinterpolationKey], [intKey], algorithmKeys])
  fns |= combineAll([rootRoot], [[reachKey], [threeTwoBitKey], [solverSMTInterpolKey, solverPrincessKey], [treeinterpolationKey], [intKey], algorithmKeys])
  
  fns |= combineAll([memsafetyRoot], [[memsafetyKey], [threeTwoBitKey], [solverZ3Key], [nestedinterpolationKey], [intKey], algorithmKeys])
  fns |= combineAll([memsafetyRoot], [[memsafetyKey], [threeTwoBitKey], [solverSMTInterpolKey, solverPrincessKey], [treeinterpolationKey], [intKey], algorithmKeys])

  fns |= combineAll([bitvectorRoot], [[reachKey], [threeTwoBitKey], [solverZ3Key], [nestedinterpolationKey], [bitvectorKey], algorithmKeys])

  return fns

for root, fn in sorted(generateFileNames()):
  #print(os.path.join(root, fn))
  writeSettingsFile(root, fn)


#for root, dirs, files in os.walk("."):
# for fn in files:
#  if fn[-4:] == '.epf':
#   writeSettingsFile(root, fn)
    
    


