import os

def writeSettingsFile(path, fn) :
  fnWPath = os.path.join(path, fn)
  print('writing to file: ', fnWPath)
  f = open(fnWPath, 'w')

  #common -- BlockEncoding
  print(standards_for_all, file=f)
  #print("", file=f)

  #RCFGBuilder
  if 'Bitvector' in fn:
   print(rcfgBuilder_bv, file=f)
  elif 'Float' in fn:
   print(rcfgBuilder_float, file=f)
  elif 'Integer' in fn:
   print(rcfgBuilder_nonbv, file=f)
  else:
   print('ERROR: neither Integer nor Bitvector in filename')

  #C translation 
  if 'Reach' in fn and 'Bitvector' in fn:
    print(cacsl_reach_bv, file=f)
  elif 'Reach' in fn and 'Float' in fn:
    print(cacsl_reach_float, file=f)
  elif 'Reach' in fn and 'Integer' in fn:
    print(cacsl_reach_nonbv, file=f)
  elif 'DerefFreeMemtrack' in fn and 'Integer' in fn:
    print(cacsl_memsafety_nonbv, file=f)
  else:
   print('ERROR: did not recognize translation mode')

  #codecheck interpolation settings
  print(dateline, file=f)
  print(codecheckCommon, file=f)

  if 'TreeInterpolation' in fn:
   print(treeItp, file=f)
  elif 'NestedInterpolation' in fn:
   print(nestedItp, file=f)
  elif 'FP' in fn:
   print(fpItp, file=f)
  elif 'BP' in fn:
   print(bpItp, file=f)
  else:
   print('ERROR: did not recognize interpolation mode')

  if 'SMTInterpol' in fn:
   print(chooseSMTInterpol, file=f)
  elif solverZ3Key in fn and nestedinterpolationKey in fn and 'Integer' in fn:
   print(chooseIZ3, file=f)
  elif solverZ3Key in fn and nestedinterpolationKey in fn and 'Bitvector' in fn:
   print(chooseIZ3_bv, file=f)
  elif '-Z3-' in fn and 'Integer' in fn:
   print(chooseExternalDefault, file=f)
  elif '-Z3-' in fn and 'Bitvector' in fn:
   print(chooseExternalDefault_bv, file=f)
  elif '-Z3-' in fn and 'Float' in fn:
   print(chooseExternalDefault_bv, file=f)
  elif 'Princess' in fn:
   print(choosePrincess, file=f)
  elif 'CVC4' in fn and 'Integer' in fn:
   print(chooseCvc4, file=f)
  elif 'CVC4' in fn and 'Bitvector' in fn:
   print(chooseCvc4_bv, file=f)
  elif 'Mathsat' in fn and 'Integer' in fn:
   print(chooseMathsat, file=f)
  elif 'Mathsat' in fn and 'Bitvector' in fn:
   print(chooseMathsat_bv, file=f)
  elif 'Mathsat' in fn and 'Float' in fn:
   print(chooseMathsat_float, file=f)
  else:
   print('ERROR: did not recognize solver to use')

  if 'LV' not in fn:
   print(dontUseLV, file=f)
  elif 'LV' in fn:
   print(useLV, file=f)

  if 'UC' not in fn:
   print(dontUseUC, file=f)
  elif 'UC' in fn:
   print(useUC, file=f)

  #codecheck set algorithm
  if 'Kojak' in fn:
   print(useKojakAlgorithm, file=f)
  elif 'Impulse' in fn:
   print(useImpulseAlgorithm, file=f)


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
/instance/de.uni_freiburg.informatik.ultimate.boogie.procedureinliner/to\ procedures,\ called\ more\ than\ once=true
'''

rcfgBuilder_bv = '''#Fri Oct 24 16:34:36 CEST 2014
\!/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder=
file_export_version=3.0
@de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder=0.0.1
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Convert\ code\ blocks\ to\ CNF=false
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Size\ of\ a\ code\ block=SequenceOfStatements
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Command\ for\ external\ solver=z3 SMTLIB2_COMPLIANT\=true -memory\:2024 -smt2 -in -t\:2000
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Logic\ for\ external\ solver=AUFBV
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Dump\ SMT\ script\ to\ file=false
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/To\ the\ following\ directory=./dump/
 '''

rcfgBuilder_float = '''#Fri Oct 24 16:34:36 CEST 2014
\!/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder=
file_export_version=3.0
@de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder=0.0.1
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Convert\ code\ blocks\ to\ CNF=false
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Size\ of\ a\ code\ block=SequenceOfStatements
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Command\ for\ external\ solver=z3 SMTLIB2_COMPLIANT\=true -memory\:2024 -smt2 -in -t\:2000
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Logic\ for\ external\ solver=ALL
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Dump\ SMT\ script\ to\ file=false
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/To\ the\ following\ directory=./dump/
 '''



rcfgBuilder_nonbv = '''#Fri Oct 24 16:34:36 CEST 2014
\!/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder=
file_export_version=3.0
@de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder=0.0.1
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Convert\ code\ blocks\ to\ CNF=false
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Size\ of\ a\ code\ block=SequenceOfStatements
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Command\ for\ external\ solver=z3 SMTLIB2_COMPLIANT\=true -memory\:2024 -smt2 -in -t\:2000
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/Dump\ SMT\ script\ to\ file=false
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder/To\ the\ following\ directory=./dump/
 '''

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
@de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator=0.0.1
 '''

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
@de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator=0.0.1
 '''

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
@de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator=0.0.1
 '''


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
@de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator=0.0.1
 '''

dateline = '''#Wed Nov 18 19:26:57 CET 2015'''
codecheckCommon = '''@de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck=0.0.1
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Use\ standard\ solver\ (from\ RCFGBuilder)\ with\ FP\ interpolation\ as\ fallback=false
file_export_version=3.0'''

treeItp = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/interpolation\ mode=Craig_TreeInterpolation'''
nestedItp = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/interpolation\ mode=Craig_NestedInterpolation'''
fpItp = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/interpolation\ mode=ForwardPredicates'''
bpItp = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/interpolation\ mode=BackwardPredicates'''

chooseExternalDefault = '''
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Use\ separate\ solver\ for\ tracechecks=true
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Choose\ which\ separate\ solver\ to\ use\ for\ tracechecks=External_ModelsAndUnsatCoreMode
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Theory\ for\ external\ solver=AUFNIRA
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Command\ for\ calling\ external\ solver=z3 SMTLIB2_COMPLIANT\=true -memory\:2024 -smt2 -in -t\:2000'''

chooseIZ3 = '''
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Use\ separate\ solver\ for\ tracechecks=true
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Choose\ which\ separate\ solver\ to\ use\ for\ tracechecks=External_Z3InterpolationMode
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Theory\ for\ external\ solver=AUFNIRA
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Command\ for\ calling\ external\ solver=z3 SMTLIB2_COMPLIANT\=true -memory\:2024 -smt2 -in -t\:2000'''

chooseSMTInterpol = '''
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Use\ separate\ solver\ for\ tracechecks=true
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Choose\ which\ separate\ solver\ to\ use\ for\ tracechecks=External_SMTInterpolInterpolationMode
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Theory\ for\ external\ solver=QF_AUFLIRA
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Command\ for\ calling\ external\ solver=smtinterpol -q -t 12000'''

choosePrincess = '''
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Use\ separate\ solver\ for\ tracechecks=true
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Choose\ which\ separate\ solver\ to\ use\ for\ tracechecks=External_PrincessInterpolationMode
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Theory\ for\ external\ solver=AUFNIRA
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Command\ for\ calling\ external\ solver=princess +incremental +stdin -timeout=12000'''

chooseCvc4 = '''
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Use\ separate\ solver\ for\ tracechecks=true
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Choose\ which\ separate\ solver\ to\ use\ for\ tracechecks=External_ModelsAndUnsatCoreMode
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Theory\ for\ external\ solver=AUFLIRA
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Command\ for\ calling\ external\ solver=cvc4 --tear-down-incremental --rewrite-divk --print-success --lang smt --tlimit-per\=12000
'''

chooseMathsat = '''
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Use\ separate\ solver\ for\ tracechecks=true
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Choose\ which\ separate\ solver\ to\ use\ for\ tracechecks=External_ModelsAndUnsatCoreMode
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Theory\ for\ external\ solver=AUFNIRA
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Command\ for\ external\ solver=mathsat
'''

chooseExternalDefault_bv = '''
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Use\ separate\ solver\ for\ tracechecks=true
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Choose\ which\ separate\ solver\ to\ use\ for\ tracechecks=External_ModelsAndUnsatCoreMode
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Theory\ for\ external\ solver=AUFBV
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Command\ for\ calling\ external\ solver=z3 SMTLIB2_COMPLIANT\=true -memory\:2024 -smt2 -in -t\:12000'''

chooseIZ3_bv = '''
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Use\ separate\ solver\ for\ tracechecks=true
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Choose\ which\ separate\ solver\ to\ use\ for\ tracechecks=External_Z3InterpolationMode
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Theory\ for\ external\ solver=AUFBV
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Command\ for\ calling\ external\ solver=z3 SMTLIB2_COMPLIANT\=true -memory\:2024 -smt2 -in -t\:12000'''

chooseCvc4_bv = '''
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Use\ separate\ solver\ for\ tracechecks=true
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Choose\ which\ separate\ solver\ to\ use\ for\ tracechecks=External_ModelsAndUnsatCoreMode
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Theory\ for\ external\ solver=AUFBV
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Command\ for\ calling\ external\ solver=cvc4 --tear-down-incremental --rewrite-divk --print-success --lang smt --tlimit-per\=12000
'''

chooseMathsat_bv = '''
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Use\ separate\ solver\ for\ tracechecks=true
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Choose\ which\ separate\ solver\ to\ use\ for\ tracechecks=External_ModelsAndUnsatCoreMode
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Theory\ for\ external\ solver=AUFBV
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Command\ for\ external\ solver=mathsat
'''

chooseMathsat_float = '''
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Use\ separate\ solver\ for\ tracechecks=true
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Choose\ which\ separate\ solver\ to\ use\ for\ tracechecks=External_ModelsAndUnsatCoreMode
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/Theory\ for\ external\ solver=AUFBV
/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Command\ for\ external\ solver=mathsat
'''




dontUseLV = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck//Use\ live\ variables\ in\ FP/BP\ interpolation=false'''
useLV = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck//Use\ live\ variables\ in\ FP/BP\ interpolation=true'''

useUC = ''''''
dontUseUC = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck//Use\ unsat\ cores\ in\ FP/BP\ interpolation=IGNORE'''

useKojakAlgorithm = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/the\ checking\ algorithm\ to\ use=ULTIMATE'''
useImpulseAlgorithm = '''/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck/the\ checking\ algorithm\ to\ use=IMPULSE'''

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
  fns |= combineAll([bitvectorRoot], [[reachKey], [threeTwoBitKey], solverKeysUc, [fpKey], [ucOnKey], [lvOnKey], [bitvectorKey], algorithmKeys])

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
  print(os.path.join(root, fn))
  writeSettingsFile(root, fn)


#for root, dirs, files in os.walk("."):
# for fn in files:
#  if fn[-4:] == '.epf':
#   writeSettingsFile(root, fn)
    
    


