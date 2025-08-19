package de.uni_freiburg.informatik.ultimate.pea2boogie.generator;

import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace.DCPhase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType.ReqPeas;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.CddToSmt;

public class RTInconsistencyPreCheck {
	public boolean mDebugReasonCOunter = true;
	public int[] reasonCounter = new int[4];
	
	private Script mScript;
	private ManagedScript mManagedScript;
	private ILogger mLogger;
	private CddToSmt mCddToSmt;
	private IUltimateServiceProvider mServices;
	public int mCombinationNum;
	public Term mDebugTerm;
	public List<ReqsWithAttributes> mListChainLinkReqs = new ArrayList<>();
	public Map<TermVariable, List<ReqsWithAttributes>> mDictVar = new HashMap<>();
	
	public List<Entry<PatternType<?>, PhaseEventAutomata>[]> mRTIReturnSet;
	public List<List<ReqsWithAttributes>> mRTICombinations = new ArrayList<>();
	


	public class ReqsWithAttributes {
		public String mName;
		public Phase mPenultimatePhase ;
		public Phase mMaxPhase;
		public Phase mBeforeMaxPhase;
		public ReqPeas mOriginalPea;
		public PhaseEventAutomata mOriginalPeaEventAutomata;
		public Term mFullExitCondition;
		public Term[] mExitConditions;
		public boolean mChainLinkReq;
		public CounterTrace mCounterTrace;
		

		public ReqsWithAttributes(final ReqPeas reqPea) {
			mOriginalPea = reqPea;
			mChainLinkReq = false;
		}

		public String getName() {
			return mName;
			
		}

	}
	
	public class Phase{
		DCPhase mDCPhase;
		Term mInvariant;
		TermVariable[] mInvariantVar;
		Term mBound;
		public Phase(DCPhase dcPhase) {
			mDCPhase = dcPhase;

		}
		
	}

	public List<Entry<PatternType<?>, PhaseEventAutomata>[]> doRtiPreCheck(final List<ReqPeas> reqPeas,
			final ILogger logger, final Script script, final CddToSmt cddToSmt, final IUltimateServiceProvider services,
			final ManagedScript managedScript, final int range) {
	    mScript = script;
	    mManagedScript = managedScript;
        mLogger = logger;
        mCddToSmt = cddToSmt;
        mServices = services;
        mRTIReturnSet = new ArrayList<>();
        mCombinationNum = range;
        
		mDebugTerm = null;
        
        
		for (final ReqPeas reqPea : reqPeas) {
        	for (final Entry<CounterTrace, PhaseEventAutomata> reqChild : reqPea.getCounterTrace2Pea()) {
        		ReqsWithAttributes newReq = new ReqsWithAttributes(reqPea);
        		newReq.mName = reqChild.getValue().getName();
        		newReq.mOriginalPeaEventAutomata = reqChild.getValue();
        		

        		//penultimate Phase
        		newReq.mPenultimatePhase = new Phase(reqChild.getKey().getPhases()[reqChild.getKey().getPhases().length - 2]);
        		newReq.mPenultimatePhase.mInvariant =  mCddToSmt.toSmt(reqChild.getKey().getPhases()[reqChild.getKey().getPhases().length - 2].getInvariant());
        		TermVariable[] vars = newReq.mPenultimatePhase.mInvariant.getFreeVars();
				for (TermVariable var : vars) {
					if (var.getName().equals("x")) {
						// if the variable is x, we can just skip it
						mDebugTerm = var;
						break;
					} 
				}

        	}
		}
        getAttribtes(reqPeas);
        rtiCheckSingles();
        rtiCheckChainLinkReqs();
        
        mLogger.info("RTI PreCheck found " + this.mRTIReturnSet.size() + " sets");
		for (Entry<PatternType<?>, PhaseEventAutomata>[] entry : this.mRTIReturnSet) {
			StringBuilder sb = new StringBuilder();
			sb.append("[");
			for (Entry<PatternType<?>, PhaseEventAutomata> e : entry) {
				sb.append(e.getValue().getName()+ " ");
			}
			sb.append("]");
			mLogger.info(sb.toString());
		}
        return mRTIReturnSet;
        
	}

	private void rtiCheckChainLinkReqs() {
		if(this.mCombinationNum > 0) {
			for(int counter = 1; counter <= this.mCombinationNum; counter++) {
				mLogger.info("DEPTH " + counter);
              
              for(ReqsWithAttributes req : this.mListChainLinkReqs) {
            	  List<ReqsWithAttributes>testSet = new ArrayList<>();
            	  testSet.add(req);
            	  Term joinedEC = req.mFullExitCondition;
            	  int chainLinkCounter = this.mListChainLinkReqs.indexOf(req);
              
            	  addChainLinkRecursive(chainLinkCounter, testSet, joinedEC, counter);

				}
              }
			
		}
		
	}

	private void addChainLinkRecursive(int startIdx,
            List<ReqsWithAttributes> testSet,
            Term joinedEC,
            int counter) {

	// Basisfälle
	if (testSet.size() == counter) {
	fillwithSingles(testSet, joinedEC);
	return;
	}
	if (testSet.size() > counter) {
	return;
	}
	
	for (int i = startIdx + 1; i < this.mListChainLinkReqs.size(); i++) {
	ReqsWithAttributes req = this.mListChainLinkReqs.get(i);
	
	if (ChainLinkTest(joinedEC.getFreeVars(),
	   req.mFullExitCondition.getFreeVars())) {
	
	mLogger.info("adding " + req.mName);
	
	// wählen
	testSet.add(req);
	
	// NICHT joinedEC überschreiben; lokale, erweiterte Variante bilden
	Term nextJoinedEC = SmtUtils.and(mScript, joinedEC, req.mFullExitCondition);
	
	// weitergehen
	addChainLinkRecursive(i, testSet, nextJoinedEC, counter);
	
	// backtrack: Auswahl rückgängig machen
	testSet.remove(testSet.size() - 1);
	} else {
	mLogger.info("not adding " + req.mName + " because of ChainLinkTest");
	}
	}
	}

	private void fillwithSingles(List<ReqsWithAttributes> testSet, Term joinedEC) {
		mLogger.info("try to fill with singles");
		joinedEC = testSet.get(0).mFullExitCondition;
		for(int i = 1; i < testSet.size(); i++) {
			joinedEC = SmtUtils.and(mScript, joinedEC, testSet.get(i).mFullExitCondition);
		}
	    joinedEC = SmtUtils.toDnf(mServices, mManagedScript, joinedEC);
	    Term[] exitConditions = SmtUtils.getDisjuncts(joinedEC);
	    List<List<ReqsWithAttributes>> list = new ArrayList<>();
	    boolean help = true;

	    
	    for (final Term exitOption : exitConditions) {
	        final List<ReqsWithAttributes> helpList = new ArrayList<>();
	        final TermVariable[] Variables = exitOption.getFreeVars();

	        for (final TermVariable variable : Variables) {
	            mLogger.info(variable);
	            if (this.mDictVar.containsKey(variable) && mDictVar.get(variable).size() > 0) {
	                helpList.addAll(mDictVar.get(variable));
	            }
	        }

	        if (helpList.size() != 0) {
	            list.add(helpList);
	        } else {
	            mLogger.info("keine rti möglich");
	            help = false;
	        }
	    }
	        if (help) {
	            mLogger.info("erstmal " + cartesianProduct(list).size());

	            for (final List<ReqsWithAttributes> reqCombo : cartesianProduct(list)) {
	                mLogger.info("neuer Vergleich");
					for (final ReqsWithAttributes req : testSet) {
						mLogger.info("chainLink enthält " + req.mName);
					}
					for( final ReqsWithAttributes req : reqCombo) {
						mLogger.info("single enthält " + req.mName);
					}

	                if (!this.mRTICombinations.contains(reqCombo)) {
	                    boolean alreadyContained = false;

	                    for (final List<ReqsWithAttributes> rtisFound : mRTICombinations) {
	                        if (reqCombo.containsAll(rtisFound)) {
	                            mLogger.info("rausgeschmissen weil schon drin");
	                            alreadyContained = true;
	                            break;
	                        }
	                    }

	                    if (!alreadyContained) {
	                        final List<ReqsWithAttributes> ll = new ArrayList<>(reqCombo);
	                        ll.addAll(testSet);

	                        if (!makePreCheckFromList(ll)) {
	                        	mRTICombinations.add(ll);
	                        	this.mRTIReturnSet.add(rtiSetsFormatted(ll));
	                        	 mLogger.info("RTI WITH CHAINLINK FOUND");
	                        } else {
	                        	mLogger.info("RTI WITH CHAINLINK NOT FOUND");
	                        }
	                       
	                    }
	                }
	            }
	        }
	        
	    }
	
	
	private boolean makePreCheckFromList(final List<ReqsWithAttributes> reqs) {
		// check exit conditions
		Term combination = reqs.get(0).mFullExitCondition;
		for (int i = 1; i < reqs.size(); i++) {
			combination = SmtUtils.and(mScript, combination, reqs.get(i).mFullExitCondition);
		}
		LBool result = SmtUtils.checkSatTerm(mScript, combination);
		if (result == LBool.SAT) {
			return true;
		}

		combination = reqs.get(0).mMaxPhase.mInvariant;
		for (int i = 1; i < reqs.size(); i++) {
			combination = SmtUtils.and(mScript, combination, reqs.get(i).mMaxPhase.mInvariant);
		}
		result = SmtUtils.checkSatTerm(mScript, combination);
		if (result == LBool.UNSAT) {
			return true;
		}
		return false;
	}

	public static <ReqWithRTIPCattributes> List<List<ReqWithRTIPCattributes>>
	cartesianProduct(final List<List<ReqWithRTIPCattributes>> lists) {
		List<List<ReqWithRTIPCattributes>> result = new ArrayList<>();
		result.add(new ArrayList<>()); // Start with empty combination

		for (final List<ReqWithRTIPCattributes> sublist : lists) {
			final List<List<ReqWithRTIPCattributes>> temp = new ArrayList<>();
			for (final List<ReqWithRTIPCattributes> combination : result) {
				for (final ReqWithRTIPCattributes element : sublist) {
					final List<ReqWithRTIPCattributes> newCombination = new ArrayList<>(combination);
					newCombination.add(element);

					// Remove duplicates manually
					final List<ReqWithRTIPCattributes> deduped = new ArrayList<>();
					for (final ReqWithRTIPCattributes item : newCombination) {
						if (!deduped.contains(item)) {
							deduped.add(item);
						}
					}

					temp.add(deduped);
				}
			}
			result = temp;
		}
		return result;
	}



	private boolean ChainLinkTest(TermVariable[] exitCinditions1, TermVariable[] exitConditions2) {
		if (habenSchnittmenge(exitCinditions1, exitConditions2)) {
			return false; // Überschneidung gefunden
		}
		
		return true;
	}
	
	public static <T> boolean habenSchnittmenge(final TermVariable[] vars1, final TermVariable[] variables) {
		for (final TermVariable elem : variables) {
			if (Arrays.asList(vars1).contains(elem)) {
				return true; // Überschneidung gefunden
			}
		}
		return false; // Keine gemeinsamen Elemente
	}

	private void rtiCheckSingles() {
		for(Entry variablesEntry: this.mDictVar.entrySet()) {
			 List<List<ReqsWithAttributes>> combinations = combinations2((List<ReqsWithAttributes>) variablesEntry.getValue());
			 for(List<ReqsWithAttributes> pair : combinations) {
				 List<ReqsWithAttributes> psorted = new ArrayList<>(pair);
				 psorted.sort(Comparator.comparing(ReqsWithAttributes::getName));

				 if(this.mRTICombinations.contains(psorted)) {
					 continue; // already checked this combination
				 }


                 if(rtiCheckFor2Reqs(pair.get(0), pair.get(1))) {
	                mLogger.info("RTI found for " + pair.get(0).mName + " and " + pair.get(1).mName);
	                this.mRTIReturnSet.add(rtiSetsFormatted(pair));
                 }
			 }

			
		}
		// TODO Auto-generated method stub
		
	}
	
	private boolean rtiCheckFor2Reqs(ReqsWithAttributes reqsWithAttributes, ReqsWithAttributes reqsWithAttributes2) {
		mLogger.info("RTI check for " + reqsWithAttributes.mName + " and " + reqsWithAttributes2.mName);
		mLogger.info(reqsWithAttributes.mCounterTrace);
		mLogger.info(reqsWithAttributes2.mCounterTrace);
		boolean help = true;

		Term conjunction = SmtUtils.and(mScript, reqsWithAttributes.mFullExitCondition, reqsWithAttributes2.mFullExitCondition);
		LBool result = SmtUtils.checkSatTerm(mScript, conjunction);
		if (result != LBool.UNSAT) {
			mLogger.info("aussportiert wegen ExitCondition passen nicht");
			if (mDebugReasonCOunter) {
				help = false;
				reasonCounter[0]++;
			} else {
				return false; // Exit conditions are not disjoint
			}
			
			
			//return false;
		}
		if (reqsWithAttributes.mBeforeMaxPhase != null && reqsWithAttributes2.mBeforeMaxPhase != null) {
			if (reqsWithAttributes.mPenultimatePhase.mBound
					.equals(reqsWithAttributes2.mPenultimatePhase.mBound)) {
				if (reqsWithAttributes.mPenultimatePhase.mBound == reqsWithAttributes2.mPenultimatePhase.mBound) {

					conjunction = SmtUtils.and(mScript, reqsWithAttributes.mBeforeMaxPhase.mInvariant,
							reqsWithAttributes2.mBeforeMaxPhase.mInvariant);
					result = SmtUtils.checkSatTerm(mScript, conjunction);
					if (result == LBool.UNSAT) {
						mLogger.info("aussportiert wegen BeforeMaxPhase invariant");
						if (mDebugReasonCOunter) {
							help = false;
							reasonCounter[3]++;
						} else {
							return false; // Exit conditions are not disjoint
						}
					}
				}


				
			}

		}
		this.mRTICombinations.add(Arrays.asList(reqsWithAttributes, reqsWithAttributes2));
		conjunction = SmtUtils.and(mScript, reqsWithAttributes.mMaxPhase.mInvariant, reqsWithAttributes2.mMaxPhase.mInvariant);
		result = SmtUtils.checkSatTerm(mScript, conjunction);
		if (result == LBool.UNSAT) {
			mLogger.info("aussportiert wegen MaxPhase invariant");
			if (mDebugReasonCOunter) {
				help = false;
				reasonCounter[1]++;
			} else {
				return false; // Exit conditions are not disjoint
			}
		}
		/*if (reqsWithAttributes.mMaxPhase == reqsWithAttributes2.mMaxPhase) {
			conjunction = SmtUtils.and(mScript, reqsWithAttributes.mMaxPhase.mBound, reqsWithAttributes2.mMaxPhase.mBound);
			result = SmtUtils.checkSatTerm(mScript, conjunction);
			if (result == LBool.UNSAT) {
				mLogger.info("aussportiert wegen MaxPhase Bound");
				if (mDebugReasonCOunter) {
					help = false;
					reasonCounter[2]++;
				} else {
					return false; // Exit conditions are not disjoint
				}
			}

		}*/
		
	
		// TODO Auto-generated method stub
		if (!help) {
			return false;
		} else {
			return true;
		}
		
	}

	public static List<List<ReqsWithAttributes>> combinations2 (List<ReqsWithAttributes> args) {
        List<List<ReqsWithAttributes>> pairs = new ArrayList<>();

        for (int i = 0; i < args.size(); i++) {
            for (int j = i + 1; j < args.size(); j++) {
                pairs.add(Arrays.asList(args.get(i), args.get(j)));
            }
        }

        return pairs;
    }

	private void getAttribtes(List<ReqPeas> reqPeas) {
		
        for (final ReqPeas reqPea : reqPeas) {
        	for (final Entry<CounterTrace, PhaseEventAutomata> reqChild : reqPea.getCounterTrace2Pea()) {
        		ReqsWithAttributes newReq = new ReqsWithAttributes(reqPea);
        		newReq.mName = reqChild.getValue().getName();
        		newReq.mOriginalPeaEventAutomata = reqChild.getValue();
        		newReq.mCounterTrace = reqChild.getKey();
        		

        		//penultimate Phase
        		newReq.mPenultimatePhase = new Phase(reqChild.getKey().getPhases()[reqChild.getKey().getPhases().length - 2]);
        		newReq.mPenultimatePhase.mInvariant =  mCddToSmt.toSmt(reqChild.getKey().getPhases()[reqChild.getKey().getPhases().length - 2].getInvariant());
        		

        		newReq.mPenultimatePhase.mInvariantVar = newReq.mPenultimatePhase.mInvariant.getFreeVars();
        		newReq.mPenultimatePhase.mBound = BoundToSmt(newReq.mPenultimatePhase);
        		Term help = SmtUtils.not( mScript, newReq.mPenultimatePhase.mInvariant);
        		newReq.mFullExitCondition = SmtUtils.toDnf(mServices, mManagedScript,  help);
        		newReq.mExitConditions = SmtUtils.getDisjuncts(newReq.mFullExitCondition);
				if (newReq.mExitConditions.length > 1) {
					newReq.mChainLinkReq = true;
					this.mListChainLinkReqs.add(newReq);
				} else {
					TermVariable[] vars = newReq.mPenultimatePhase.mInvariant.getFreeVars();
					for (TermVariable var : vars) {
						if (!this.mDictVar.containsKey(var)) {
							this.mDictVar.put(var, new ArrayList<>());
						}
							this.mDictVar.get(var).add(newReq);
						
					}
				}
        		//Max Phase bestimmen
				if (newReq.mPenultimatePhase.mDCPhase.getBoundType() != 0) {
					newReq.mMaxPhase = new Phase(reqChild.getKey().getPhases()[reqChild.getKey().getPhases().length - 2]);
					if (reqChild.getKey().getPhases().length > 2) {
						newReq.mBeforeMaxPhase =
								new Phase(reqChild.getKey().getPhases()[reqChild.getKey().getPhases().length - 3]);
					}
				} else {
					newReq.mMaxPhase = new Phase(reqChild.getKey().getPhases()[reqChild.getKey().getPhases().length - 3]);
					if (reqChild.getKey().getPhases().length > 3) {
						newReq.mBeforeMaxPhase =
								new Phase(reqChild.getKey().getPhases()[reqChild.getKey().getPhases().length - 4]);
					}
				} 
				newReq.mMaxPhase.mInvariant =  mCddToSmt.toSmt(newReq.mMaxPhase.mDCPhase.getInvariant());
				newReq.mMaxPhase.mInvariantVar = newReq.mMaxPhase.mInvariant.getFreeVars();
				newReq.mMaxPhase.mBound = BoundToSmt(newReq.mMaxPhase);
				if(newReq.mBeforeMaxPhase != null) {
					newReq.mBeforeMaxPhase.mInvariant = mCddToSmt.toSmt(newReq.mBeforeMaxPhase.mDCPhase.getInvariant());
					newReq.mBeforeMaxPhase.mInvariantVar = newReq.mBeforeMaxPhase.mInvariant.getFreeVars();
					newReq.mBeforeMaxPhase.mBound = BoundToSmt(newReq.mBeforeMaxPhase);
					
				}
				
				
				
        	
				
        		
        		

        		

        		
        		
        	}

        	
        	
        }

		
	}
	
	public Entry<PatternType<?>, PhaseEventAutomata>[] rtiSetsFormatted(final List<ReqsWithAttributes> reqs) {
		final List<Map.Entry<PatternType<?>, PhaseEventAutomata>> entryList = new ArrayList<>();
		for (final ReqsWithAttributes req : reqs) {
			final Map.Entry<PatternType<?>, PhaseEventAutomata> entry1 =
					new AbstractMap.SimpleEntry<>(req.mOriginalPea.getPattern(), req.mOriginalPeaEventAutomata);
			entryList.add(entry1);
		}
		final Map.Entry<PatternType<?>, PhaseEventAutomata>[] entryArray = entryList.toArray(new Map.Entry[0]);
		Arrays.sort(entryArray, Comparator.comparing(Map.Entry::getValue));
		return entryArray;
	}


	private Term BoundToSmt(Phase phase) {
		Term boundTerm =  mScript.term("true");
		if (phase.mDCPhase.getBoundType() == 0) {
			return mScript.term("true");
		} else if (phase.mDCPhase.getBoundType() == 2) {
			 Term rhs = mScript.decimal(Double.toString(phase.mDCPhase.getBound()));
			 return  SmtUtils.greater(mScript, mDebugTerm, rhs);
			//t = SmtUtils.leq(mScript, startTerm, SmtUtils.term("x", phase.mDCPhase.getBound()));
			//return mScript.term("x>" + phase.mDCPhase.getBound());
			
		} else if (phase.mDCPhase.getBoundType() == 1) {
			Term rhs = mScript.decimal(Double.toString(phase.mDCPhase.getBound()));
			return SmtUtils.geq(mScript, mDebugTerm, rhs);
			// t = SmtUtils.geq(mScript, startTerm, SmtUtils.term("x", phase.mDCPhase.getBound()));
			// return mScript.term("x<" + phase.mDCPhase.getBound());
		} else if (phase.mDCPhase.getBoundType() == -2) {
			Term rhs = mScript.decimal(Double.toString(phase.mDCPhase.getBound()));
			return SmtUtils.less(mScript, mDebugTerm, rhs);
			// t = SmtUtils.eq(mScript, startTerm, SmtUtils.term("x", phase.mDCPhase.getBound()));
			// return mScript.term("x==" + phase.mDCPhase.getBound());
		}else {
			Term rhs = mScript.decimal(Double.toString(phase.mDCPhase.getBound()));
			return SmtUtils.leq(mScript, mDebugTerm, rhs);
		}

	}
}
		