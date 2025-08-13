package de.uni_freiburg.informatik.ultimate.pea2boogie.generator;

import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace.DCPhase;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType.ReqPeas;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.pea2boogie.CddToSmt;

public class RTInconsistencyPreCheck {
	private Script mScript;
	private ILogger mLogger;
	private CddToSmt mCddToSmt;
	public List<ReqWithRTIPCattributes> mListWithChainLinkReqs;
	public Map<TermVariable, List<ReqWithRTIPCattributes>> VariablesDict;
	public List<Entry<PatternType<?>, PhaseEventAutomata>[]> mrtiSets;
	public int mCombinationNum;

	public class ReqWithRTIPCattributes {
		public String mName; // not important, just for debug reasons
		public ReqPeas mOriginalPea;
		public DCPhase mPenultimatePhase;
		public DCPhase mMaxPhase;
		public PhaseEventAutomata mPEA;

		public List<Term> mExitOptions;
		public Term mFullExitOption;
		public Term mTermInvariantMaxPhase;
		public boolean mChainLinkReq;
		public Term mPhaseBeforeMaxPhase;

		public ReqWithRTIPCattributes(ReqPeas reqPea) {
			mOriginalPea = reqPea;
		}
	}

	/**
	 * This method is used to check the RTI sets of the requirements. First single
	 * reqs (so depth of search = 2), later sets with chain-link requirements (depth
	 * of search >= 3)
	 * 
	 * @param reqs List of ReqWithRTIPCattributes containing the requirements to be
	 *             formatted.
	 * @return An array of Map.Entry objects representing the formatted RTI sets.
	 */
	public List<Entry<PatternType<?>, PhaseEventAutomata>[]> doRtiPreCheck(List<ReqPeas> reqPeas, ILogger logger,
			Script script, CddToSmt cddToSmt, int combinationNum) {
		mScript = script;
		mLogger = logger;
		mCddToSmt = cddToSmt;
		mCombinationNum = combinationNum;
		mListWithChainLinkReqs = new ArrayList<>();
		VariablesDict = new HashMap();
		mrtiSets = new ArrayList<>();

		getAttributesForReqs(reqPeas);

		for (Map.Entry<TermVariable, List<ReqWithRTIPCattributes>> varialesList : VariablesDict.entrySet()) {
			for (int i = 0; i < varialesList.getValue().size(); i++) {
				ReqWithRTIPCattributes req1 = varialesList.getValue().get(i);

				for (int j = i + 1; j < varialesList.getValue().size(); j++) {
					ReqWithRTIPCattributes req2 = varialesList.getValue().get(j);
					mLogger.info("---------Neuer Vergleich---------");
					mLogger.info(req1.mName);
					mLogger.info(req2.mName);

					Entry<PatternType<?>, PhaseEventAutomata>[] combo = rtiSetsFormatted(Arrays.asList(req1, req2));
					if (!mrtiSets.contains(combo)) {
						if (!makePreCheck(req1, req2)) {
							mrtiSets.add(combo);
						}
					}
				}
			}
		}

		if (mCombinationNum >= 3) {
			mLogger.info("START DOING CHAIN REQS");
			for (ReqWithRTIPCattributes req : mListWithChainLinkReqs) {
				mLogger.info("---------Neuer Vergleich---------");
				mLogger.info(req.mName);
				mLogger.info(req.mOriginalPea.getPattern().toString());
				List<List<ReqWithRTIPCattributes>> list = new ArrayList<>();

				for (Term exitOption : req.mExitOptions) {
					List<ReqWithRTIPCattributes> helpList = new ArrayList<>();
					TermVariable[] Variables = exitOption.getFreeVars();
					for (TermVariable variable : Variables) {
						mLogger.info(variable);
						if (VariablesDict.containsKey(variable) && VariablesDict.get(variable).size() > 0) {
							helpList.addAll(VariablesDict.get(variable));
						}
					}
					list.add(helpList);
				}

				for (List<ReqWithRTIPCattributes> reqCombo : cartesianProduct(list)) {
					if (!mrtiSets.contains(reqCombo)) {
						List<ReqWithRTIPCattributes> ll = reqCombo;
						ll.add(req);
						if (!makePreCheckFromList(ll)) {
							if (!mrtiSets.contains(rtiSetsFormatted(ll))) {
								mrtiSets.add(rtiSetsFormatted(ll));
								mLogger.info("RTI WITH CHIANLINKL FOUND");
							}
						}
					}
				}
			}
		}

		mLogger.info("PreCheck found possible rt-inconsistent sets::");
		mLogger.info("Number of sets: " + mrtiSets.size());
		for (Entry<PatternType<?>, PhaseEventAutomata>[] rtiSet : mrtiSets) {
			mLogger.info("----------RTI SET-----------:");
			for (Entry<PatternType<?>, PhaseEventAutomata> entry : rtiSet) {
				mLogger.info(entry.getValue().getName() + ":" + entry.getKey().toString());
			}
		}

		return mrtiSets;
	}

	/**
	 * Formats the RTI sets into an array of entries with PatternType and
	 * PhaseEventAutomata. This Format is needed for the actual RTI check in the
	 * BoogieGenerator.
	 * 
	 * @param reqs List of ReqWithRTIPCattributes containing the requirements to be
	 *             formatted.
	 * @return An array of Map.Entry objects representing the formatted RTI sets.
	 */
	public Entry<PatternType<?>, PhaseEventAutomata>[] rtiSetsFormatted(List<ReqWithRTIPCattributes> reqs) {
		List<Map.Entry<PatternType<?>, PhaseEventAutomata>> entryList = new ArrayList<>();
		for (ReqWithRTIPCattributes req : reqs) {
			Map.Entry<PatternType<?>, PhaseEventAutomata> entry1 = new AbstractMap.SimpleEntry<>(
					req.mOriginalPea.getPattern(), req.mPEA);
			entryList.add(entry1);
		}
		Map.Entry<PatternType<?>, PhaseEventAutomata>[] entryArray = entryList.toArray(new Map.Entry[0]);
		Arrays.sort(entryArray, Comparator.comparing(Map.Entry::getValue));
		return entryArray;
	}

	/**
	 * Computes the Cartesian product of a list of lists of Requirements.
	 * 
	 * @param lists A list of lists, where each sublist contains elements to be
	 *              combined.
	 * @return A list containing all combinations of elements from the input lists.
	 */
	public static <ReqWithRTIPCattributes> List<List<ReqWithRTIPCattributes>> cartesianProduct(
			List<List<ReqWithRTIPCattributes>> lists) {
		List<List<ReqWithRTIPCattributes>> result = new ArrayList<>();
		result.add(new ArrayList<>()); // Start with empty combination

		for (List<ReqWithRTIPCattributes> sublist : lists) {
			List<List<ReqWithRTIPCattributes>> temp = new ArrayList<>();
			for (List<ReqWithRTIPCattributes> combination : result) {
				for (ReqWithRTIPCattributes element : sublist) {
					List<ReqWithRTIPCattributes> newCombination = new ArrayList<>(combination);
					newCombination.add(element);

					// Remove duplicates manually
					List<ReqWithRTIPCattributes> deduped = new ArrayList<>();
					for (ReqWithRTIPCattributes item : newCombination) {
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

	/*
	 * This method is used to check if the two requirements are rt-inconsistent.
	 * RETURN true if they are rt-consistent RETURN false if they are
	 * rt-inconsistent
	 */
	private boolean makePreCheck(ReqWithRTIPCattributes req1, ReqWithRTIPCattributes req2) {
		// check exit conditions
		Term combination = SmtUtils.and(mScript, req1.mFullExitOption, req2.mFullExitOption);
		LBool result = SmtUtils.checkSatTerm(mScript, combination);
		if (result != LBool.UNSAT) {
			return true;
		}
		// Check if the Max Phases can be combined
		combination = SmtUtils.and(mScript, req1.mTermInvariantMaxPhase, req2.mTermInvariantMaxPhase);
		result = SmtUtils.checkSatTerm(mScript, combination);
		if (result == LBool.UNSAT) {
			return true;
		}

		if (req1.mMaxPhase.getBoundType() != 0 && req2.mMaxPhase.getBoundType() != 0
				&& req1.mTermInvariantMaxPhase == req2.mTermInvariantMaxPhase) {
			if ((req1.mMaxPhase.getBoundType() > 0) && req2.mMaxPhase.getBoundType() < 0) {
				if (req1.mMaxPhase.getBound() > req2.mMaxPhase.getBound()) {
					return true;
				}
			}
		}

		if (req2.mMaxPhase.getBoundType() != 0 && req1.mMaxPhase.getBoundType() != 0
				&& req1.mTermInvariantMaxPhase == req2.mTermInvariantMaxPhase) {
			if ((req2.mMaxPhase.getBoundType() > 0) && req2.mMaxPhase.getBoundType() < 0) {
				if (req2.mMaxPhase.getBound() > req1.mMaxPhase.getBound()) {
					return true;
				}
			}
		}

		if (req1.mPenultimatePhase.getBoundType() == req2.mPenultimatePhase.getBoundType()) {
			if (req1.mPenultimatePhase.getBound() == req2.mPenultimatePhase.getBound()) {
				combination = SmtUtils.and(mScript, req1.mPhaseBeforeMaxPhase, req2.mPhaseBeforeMaxPhase);
				result = SmtUtils.checkSatTerm(mScript, combination);
				if (result == LBool.UNSAT) {
					return true;
				}
			}
		}
		return false;
	}

	private boolean makePreCheckFromList(List<ReqWithRTIPCattributes> reqs) {
		// check exit conditions
		Term combination = reqs.get(0).mFullExitOption;
		for (int i = 1; i < reqs.size(); i++) {
			combination = SmtUtils.and(mScript, combination, reqs.get(i).mFullExitOption);
		}
		LBool result = SmtUtils.checkSatTerm(mScript, combination);
		if (result == LBool.SAT) {
			return true;
		}

		combination = reqs.get(0).mTermInvariantMaxPhase;
		for (int i = 1; i < reqs.size(); i++) {
			combination = SmtUtils.and(mScript, combination, reqs.get(i).mTermInvariantMaxPhase);
		}
		result = SmtUtils.checkSatTerm(mScript, combination);
		if (result == LBool.UNSAT) {
			return true;
		}
		return false;
	}

	/*
	 * This method is used to get all the attributes of the requirements needed of
	 * the precheck. Containing PenultimatePhase, MaxPhase, FullExitOption,
	 * TermInvariantMaxPhase
	 */
	private void getAttributesForReqs(List<ReqPeas> reqPeas) {
		for (ReqPeas reqPea : reqPeas) {
			for (Entry<CounterTrace, PhaseEventAutomata> reqChild : reqPea.getCounterTrace2Pea()) {
				ReqWithRTIPCattributes newReq = new ReqWithRTIPCattributes(reqPea);
				mLogger.info(reqChild.getValue().getName()); // DEBUG
				newReq.mName = reqChild.getValue().getName(); // just for DEBUG reason

				// penultimate Phase
				newReq.mPenultimatePhase = reqChild.getKey().getPhases()[reqChild.getKey().getPhases().length - 2];
				CDD[] exitOptionsCDD = newReq.mPenultimatePhase.getInvariant().negate().toDNF();
				newReq.mFullExitOption = mCddToSmt.toSmt(newReq.mPenultimatePhase.getInvariant().negate());
				newReq.mPEA = reqChild.getValue();

				// generate exit Options
				newReq.mExitOptions = new ArrayList<>();
				for (CDD exitOption : exitOptionsCDD) {
					newReq.mExitOptions.add(mCddToSmt.toSmt(exitOption));
				}

				// ChainLink Reqs
				if (newReq.mExitOptions.size() > 1) {
					newReq.mChainLinkReq = true;
					mListWithChainLinkReqs.add(newReq);
				} else {
					for (TermVariable variable : newReq.mExitOptions.get(0).getFreeVars()) {
						if (!VariablesDict.containsKey(variable)) {
							VariablesDict.put(variable, new ArrayList<>());
						}
						VariablesDict.get(variable).add(newReq);
					}
				}

				// Max Phase, needed later to eliminate false positives
				if (newReq.mPenultimatePhase.getBoundType() != 0) {
					newReq.mMaxPhase = newReq.mPenultimatePhase;
					if (reqChild.getKey().getPhases().length >= 3) {
						newReq.mPhaseBeforeMaxPhase = mCddToSmt
								.toSmt(reqChild.getKey().getPhases()[reqChild.getKey().getPhases().length - 3]
										.getInvariant());
					}
				} else {
					newReq.mMaxPhase = reqChild.getKey().getPhases()[reqChild.getKey().getPhases().length - 3];
					if (reqChild.getKey().getPhases().length >= 4) {
						newReq.mPhaseBeforeMaxPhase = mCddToSmt
								.toSmt(reqChild.getKey().getPhases()[reqChild.getKey().getPhases().length - 4]
										.getInvariant());
					}
				}
				newReq.mTermInvariantMaxPhase = mCddToSmt.toSmt(newReq.mMaxPhase.getInvariant());
			}
		}
	}
}
