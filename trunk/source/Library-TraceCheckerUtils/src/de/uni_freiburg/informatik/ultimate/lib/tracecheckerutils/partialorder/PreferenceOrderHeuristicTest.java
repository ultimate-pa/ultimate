package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;

public class PreferenceOrderHeuristicTest<L extends IIcfgTransition<?>> {
	
	private Set<IcfgEdge> mFinished;
	private IIcfg<?> mIcfg;
	private List<String> mAllProcedures;
	private List<String> mLoopProcedures;
	private HashMap<String, Deque<IcfgEdge>> mPathMap;
	private Set<IProgramVar> mEffectiveGlobalVars;
	private HashMap<String, Set<IProgramVar>> mSharedVarsMap;
	private String mSequence;
	private final ManagedScript mMgdScript;
	private HashMap<String, HashMap<IProgramVar, Integer>> mLoopVarsMap;
	
	public PreferenceOrderHeuristicTest(final IIcfg<?> icfg, final List<String> allProcedures,
			final Set<IProgramVar> effectiveGlobalVars, final HashMap<String, Set<IProgramVar>> sharedVars,
			final ManagedScript mgdScript) {
		mFinished = new HashSet<>();
		mMgdScript = mgdScript;
		mIcfg = icfg;
		mAllProcedures = allProcedures;
		mLoopProcedures = new ArrayList<>();
		mPathMap = new HashMap<>();
		mEffectiveGlobalVars = effectiveGlobalVars;
		mSharedVarsMap = sharedVars;
		mLoopVarsMap = new HashMap<>();
	}
	
	public void computeParameterizedOrder() {
		for (final String procedure : mAllProcedures) {
			final IcfgLocation entryNode = mIcfg.getProcedureEntryNodes().get(procedure);
			findLoop(entryNode);
		}
		solveLES();
	}


	private void findLoop(IcfgLocation entryNode) {
		IcfgLocation goal = null;
		Map<IcfgEdge, IcfgEdge> pathMap = new HashMap<>();
		Deque<IcfgEdge> worklist = new ArrayDeque<>();
		Collection<IcfgEdge> initialEdges = entryNode.getOutgoingEdges().stream()
				.filter(mFinished::add).collect(Collectors.toSet());
		initialEdges.forEach(worklist::add);
		if (mIcfg.getLoopLocations().contains(entryNode)) {
			goal = entryNode;
			for (IcfgEdge edge : initialEdges) {
				pathMap.put(edge, null);
			}
		}		
		while(!worklist.isEmpty()) {
			final IcfgEdge currentEdge = worklist.removeFirst();
			final IcfgLocation currentTarget = currentEdge.getTarget();
			//skip edges that leave the current procedure
			if (!currentTarget.getProcedure().equals(currentEdge.getPrecedingProcedure())) {
				continue;
			}
			if (goal != null) {
				if (goal.equals(currentTarget)) {
					//loop found, backtrack and construct path
					final Deque<IcfgEdge> path = new ArrayDeque<>();
					IcfgEdge predecessor = pathMap.get(currentEdge);
					path.addFirst(currentEdge);
					while (predecessor != null) {
						path.addFirst(predecessor);
						predecessor = pathMap.get(predecessor);
					}
					
					//remove the while-condition from the path
					if (path.getFirst().getTransformula().getAssignedVars().isEmpty()) {
						path.removeFirst();
					}
					mPathMap.put(currentEdge.getPrecedingProcedure(), path);
					worklist.clear();
					
				} else {
					//continue searching
					Collection<IcfgEdge> newEdges = currentTarget.getOutgoingEdges().stream()
							.filter(mFinished::add).collect(Collectors.toSet());
					for (IcfgEdge edge : newEdges) {
						worklist.add(edge);
						pathMap.put(edge, currentEdge);
					}
				}
			} else {
				if (mIcfg.getLoopLocations().contains(currentTarget)) {
					//loophead found, start searching for the loop path
					goal = currentTarget;
					worklist.clear();
					Collection<IcfgEdge> newEdges = currentTarget.getOutgoingEdges().stream()
							.filter(mFinished::add).collect(Collectors.toSet());
					for (IcfgEdge edge : newEdges) {
						worklist.add(edge);
						pathMap.put(edge, null);
					}
				} else {
					//continue searching
					currentTarget.getOutgoingEdges().stream().filter(mFinished::add).forEachOrdered(worklist::add);
				}
			}
		}
		
	}
	
	private void solveLES() {
		// compute variable accesses
		for (String procedure : mPathMap.keySet()) {
			final Deque<IcfgEdge> path = mPathMap.get(procedure);
			mLoopProcedures.add(procedure);
			HashMap<IProgramVar, Integer> varMap = new HashMap<>();
			for (IcfgEdge edge : path) {
				Set<IProgramVar> edgeVars = new HashSet<>();
				edgeVars.addAll(edge.getTransformula().getInVars().keySet());
				edgeVars.addAll(edge.getTransformula().getOutVars().keySet());
				for (final IProgramVar var : edgeVars) {
					if (varMap.containsKey(var)) {
						final Integer value = varMap.get(var) + 1;
						varMap.put(var, value);
					} else {
						varMap.put(var, 1);
					}
				}
			}
			mLoopVarsMap.put(procedure, varMap);
		}
		
		//construct the LES
		mMgdScript.lock(this);
		mMgdScript.push(this, 1);
		var procConstants = declareProcedureConstants(mLoopProcedures);
		final var script = mMgdScript.getScript();
		final HashMap<Term, Integer> termEvaluationMap = new HashMap<>();
		

		for (final String fstProcedure : mLoopProcedures) {
			final int fstIndex = mLoopProcedures.indexOf(fstProcedure);
			if (fstIndex < mLoopProcedures.size() - 1) {
				for (int sndIndex = fstIndex + 1; sndIndex < mLoopProcedures.size(); sndIndex++) {
					// calculate the accesses on shared vars
					final String sndProcedure = mLoopProcedures.get(sndIndex);
					int fstSharedAccesses = 0;
					int sndSharedAccesses = 0;
					final HashMap<IProgramVar, Integer> fstVarMap = mLoopVarsMap.get(fstProcedure);
					final HashMap<IProgramVar, Integer> sndVarMap = mLoopVarsMap.get(sndProcedure);
					final Set<IProgramVar> sharedVars = new HashSet<>(mSharedVarsMap.get(fstProcedure));
					sharedVars.retainAll(mSharedVarsMap.get(sndProcedure));
					for (final IProgramVar var : sharedVars) {
						if (fstVarMap.containsKey(var)) {
							fstSharedAccesses += fstVarMap.get(var);
						}
						if (sndVarMap.containsKey(var)) {
							sndSharedAccesses += sndVarMap.get(var);
						}
					}

					final Rational fstSA = SmtUtils.toRational(fstSharedAccesses);
					final Rational sndSA = SmtUtils.toRational(sndSharedAccesses);
					final Term fstMul = SmtUtils.mul(script, fstSA, procConstants.get(fstProcedure));
					final Term sndMul = SmtUtils.mul(script, sndSA, procConstants.get(sndProcedure));
					final Term equation = SmtUtils.equality(script, fstMul, sndMul);
					mMgdScript.assertTerm(this, equation);
				}
			}

			// final Term procedure = script.term(fstProcedure);
			final Term zero = SmtUtils.toRational(0).toTerm(script.sort(SmtSortUtils.INT_SORT));
			final Term condition = SmtUtils.less(script, zero, procConstants.get(fstProcedure));
			mMgdScript.assertTerm(this, condition);

			termEvaluationMap.put(procConstants.get(fstProcedure), null);
		}
		
		// try to solve equation system
		String sequence = "";
		final var result = mMgdScript.checkSat(this);

		if (result != LBool.SAT) {
			// if not solvable, then calculate the accesses on shared vars for all procedures at once
			termEvaluationMap.clear();
			mMgdScript.pop(this, 1);
			mMgdScript.push(this, 1);

			procConstants = declareProcedureConstants(mLoopProcedures);
			final var dummy = SmtUtils.buildNewConstant(script, "dummy", SmtSortUtils.INT_SORT);

			for (final String procedure : mLoopProcedures) {
				int sharedAccesses = 0;
				final HashMap<IProgramVar, Integer> varMap = mLoopVarsMap.get(procedure);
				for (final IProgramVar var : varMap.keySet()) {
					if (mEffectiveGlobalVars.contains(var)) {
						sharedAccesses += varMap.get(var);
					}
				}

				final Rational procedureSA = SmtUtils.toRational(sharedAccesses);
				final Term mult = SmtUtils.mul(script, procedureSA, procConstants.get(procedure));
				final Term equation = SmtUtils.equality(script, dummy, mult);
				mMgdScript.assertTerm(this, equation);

				final Term zero = SmtUtils.toRational(0).toTerm(script.sort(SmtSortUtils.INT_SORT));
				final Term condition = SmtUtils.less(script, zero, procConstants.get(procedure));
				mMgdScript.assertTerm(this, condition);

				termEvaluationMap.put(procConstants.get(procedure), null);
			}
			mMgdScript.checkSat(this);
		}

		final var termValues = mMgdScript.getValue(this, termEvaluationMap.keySet().toArray(Term[]::new));
		for (final Term term : termEvaluationMap.keySet()) {
			final Term value = termValues.get(term);
			final var rational = SmtUtils.tryToConvertToLiteral(value);
			assert rational != null && rational.isIntegral();

			termEvaluationMap.put(term, rational.numerator().intValue());
		}

		if (!mLoopProcedures.isEmpty()) {
			for (final Term term : termEvaluationMap.keySet()) {
				final int value = termEvaluationMap.get(term);
				final int maxStep = value;
				sequence += String.format("%d,%d ", mAllProcedures.indexOf(term.toString()), maxStep);
			}
		}

		final var remainingProcedures =
				mAllProcedures.stream().filter(p -> !mLoopProcedures.contains(p)).collect(Collectors.toList());
		for (final String procedure : remainingProcedures) {
			sequence += String.format("%d,1 ", mAllProcedures.indexOf(procedure));
		}
		sequence = sequence.substring(0, sequence.length() - 1);
		mSequence = sequence;
		mMgdScript.pop(this, 1);
		mMgdScript.unlock(this);
		
	}
	
	private Map<String, Term> declareProcedureConstants(final List<String> procedures) {
		return procedures.stream().collect(Collectors.toMap(Function.identity(), this::makeProcedureConstant));
	}

	private Term makeProcedureConstant(final String name) {
		return SmtUtils.buildNewConstant(mMgdScript.getScript(), name, SmtSortUtils.INT_SORT);
	}

	public String getParameterizedOrderSequence() {
		return mSequence;
	}

	public Set<IProgramVar> getEffectiveGlobalVars() {
		return mEffectiveGlobalVars;
	}
}
