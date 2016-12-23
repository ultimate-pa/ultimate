/*
 * Copyright (C) 2016 Yu-Wen Chen
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.statistics.Benchmark;

/**
 * Create and collects @EqNode from ApplicationTerm (store and select)
 *
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 * @author Alexander Nutz
 */
public class VPDomainPreanalysis {
	
	
	private final Benchmark mBenchmark;

	private final HashRelation<IProgramVarOrConst, EqFunctionNode> mArrayIdToFnNodes = new HashRelation<>();
	private final Map<Term, EqNode> mTermToEqNode = new HashMap<>();
	private final Map<Term, IProgramVarOrConst> mTermToProgramVarOrConst = new HashMap<>();
	private final ManagedScript mManagedScript;
	private final IIcfgSymbolTable mSymboltable;
	private final NestedMap2<IProgramVarOrConst, List<EqNode>, EqFunctionNode> mEqFunctionNodeStore =
			new NestedMap2<>();
	private final Map<IProgramVarOrConst, EqAtomicBaseNode> mEqBaseNodeStore = new HashMap<>();
	private final Set<ApplicationTerm> mEquations = new HashSet<>();
	private final Set<ApplicationTerm> mSelectTerms = new HashSet<>();
	private final VPDomainPreanalysisSettings mSettings;
	/**
	 * Stores for each array, which Terms(EqNodes) are used to access it.
	 */
	private final HashRelation<IProgramVarOrConst, EqNode> mArrayToAccessingEqNodes = new HashRelation<>();
	private final ILogger mLogger;

	private final boolean mIsDebugMode = true;

	public VPDomainPreanalysis(final IIcfg<?> root, final ILogger logger) {
		mManagedScript = root.getCfgSmtToolkit().getManagedScript();
		mLogger = logger;
		mSymboltable = root.getSymboltable();
		mSettings = new VPDomainPreanalysisSettings();
		mBenchmark = new Benchmark();
		mBenchmark.start(VPSFO.overallFromPreAnalysis);
		mBenchmark.register(VPSFO.vpStateEqualsClock);
		mBenchmark.register(VPSFO.addEqualityClock);
		mBenchmark.register(VPSFO.propagateDisEqualitiesClock);
		mBenchmark.register(VPSFO.applyClock);
		mBenchmark.register(VPSFO.conjoinOverallClock);
		process(RcfgUtils.getInitialEdges(root));
	}

	private <T extends IcfgEdge> void process(final Collection<T> edges) {
		mLogger.info("started VPDomainPreAnalysis");
		

		final Deque<IcfgEdge> worklist = new ArrayDeque<>();
		final Set<IcfgEdge> finished = new HashSet<>();

		worklist.addAll(edges);
		while (!worklist.isEmpty()) {
			final IcfgEdge current = worklist.removeFirst();
			if (!finished.add(current)) {
				continue;
			}
			if (current instanceof IAction) {
				visit((IAction) current);
			}
			worklist.addAll(current.getTarget().getOutgoingEdges());
		}
	}

	
	// TODO: move to interfaces I<X>Action, the visitor is unnecessary, then
	
	protected void visit(IAction c) {
		if (c instanceof ICallAction) {
			visit((ICallAction) c);
		} else if (c instanceof IReturnAction) {
			visit((IReturnAction) c);
		} else if (c instanceof IInternalAction) {
			visit((IInternalAction) c);
		} else {
			assert false : "forgot a case?";
		}
	}

	protected void visit(ICallAction c) {
		TransFormula tf = c.getLocalVarsAssignment();
		handleTransFormula(tf);
	}

	protected void visit(IReturnAction c) {
		TransFormula tf = c.getAssignmentOfReturn();
		handleTransFormula(tf);
	}

	protected void visit(IInternalAction c) {
		TransFormula tf = c.getTransformula();
		handleTransFormula(tf);
	}

	
	private void handleTransFormula(TransFormula tf) {
		final Map<Term, Term> substitionMap =
				VPDomainHelpers.computeNormalizingSubstitution(tf);
		final Term formulaWithNormalizedVariables = new Substitution(mManagedScript, substitionMap).transform(tf.getFormula());
		
		/*
		 * handle selects in the formula
		 */
		final List<MultiDimensionalSelect> mdSelectsAll =
				MultiDimensionalSelect.extractSelectShallow(formulaWithNormalizedVariables, false);
		final List<MultiDimensionalSelect> mdSelectsFiltered =
				mSettings.trackAllArrays() ?
						mdSelectsAll :
							mdSelectsAll.stream()
							.filter(mds -> isArrayTracked(getOrConstructBoogieVarOrConst(mds.getArray())))
							.collect(Collectors.toList());
		for (final MultiDimensionalSelect mds : mdSelectsFiltered) {
			constructEqNode(mds);
		}

		/*
		 * handle stores in the formula
		 */
		final List<MultiDimensionalStore> mdStoresAll =
				MultiDimensionalStore.extractArrayStoresShallow(formulaWithNormalizedVariables);
		final List<MultiDimensionalStore> mdStoresFiltered =
				mSettings.trackAllArrays() ?
						mdStoresAll :
							mdStoresAll.stream()
							.filter(mds -> isArrayTracked(getOrConstructBoogieVarOrConst(mds.getArray())))
							.collect(Collectors.toList());
		for (final MultiDimensionalStore mds : mdStoresFiltered) {
			constructEqNode(mds);
		}

		/*
		 * Store all select-terms and equations for postprocessing
		 *
		 */
		final Set<String> equationFunctionNames = new HashSet<>(2);
		equationFunctionNames.add("=");
		equationFunctionNames.add("distinct");
		final Set<ApplicationTerm> equations = new ApplicationTermFinder(equationFunctionNames, false)
				.findMatchingSubterms(formulaWithNormalizedVariables);
		mEquations.addAll(equations);
		final Set<ApplicationTerm> selectTerms =
				mdSelectsFiltered.stream().map(mds -> mds.getSelectTerm()).collect(Collectors.toSet());
		mSelectTerms.addAll(selectTerms);

	}



	private EqNode constructEqNode(final MultiDimensionalStore mds) {
		EqNode result = mTermToEqNode.get(mds.getStoreTerm());
		if (result != null) {
			return result;
		}

		IProgramVarOrConst arrayId;
		if (!isAtomicTerm(mds.getArray())) {
			// if mds.getArray ist not a constant or variable, it must be a select, right?
			final MultiDimensionalSelect innerSelect = new MultiDimensionalSelect(mds.getArray());
			final EqFunctionNode innerSelectNode = (EqFunctionNode) constructEqNode(innerSelect);
			arrayId = innerSelectNode.getFunction();
		} else {
			arrayId = getOrConstructBoogieVarOrConst(mds.getArray());
		}

		final List<EqNode> arguments = new ArrayList<>();
		for (final Term arrayIndex : mds.getIndex()) {
			final EqNode argumentEqNode = getOrConstructEqNode(arrayIndex);
			if (argumentEqNode == null) {
				/*
				 * argument contains something we don't track
				 *  --> abort..
				 */
				return argumentEqNode;
			}
			arguments.add(argumentEqNode);
			mArrayToAccessingEqNodes.addPair(arrayId, argumentEqNode);
		}
		getOrConstructEqNode(mds.getValue());

		result = getOrConstructEqFnNode(arrayId, arguments);
		mTermToEqNode.put(mds.getStoreTerm(), result);
		return result;
	}

	private EqNode constructEqNode(final MultiDimensionalSelect mds) {
		EqNode result = mTermToEqNode.get(mds.getSelectTerm());
		if (result != null) {
			return result;
		}

		IProgramVarOrConst arrayId;
		if (!isAtomicTerm(mds.getArray())) {
			// if mds.getArray ist not a constant or variable, it must be a store, right?
			final MultiDimensionalStore innerStore = new MultiDimensionalStore(mds.getArray());
			final EqFunctionNode innerStoreNode = (EqFunctionNode) constructEqNode(innerStore);
			arrayId = innerStoreNode.getFunction();
		} else {
			arrayId = getOrConstructBoogieVarOrConst(mds.getArray());
		}

		final List<EqNode> arguments = new ArrayList<>();
		for (final Term ai : mds.getIndex()) {
			final EqNode argumentEqNode = getOrConstructEqNode(ai);
			if (argumentEqNode == null) {
				/*
				 * argument contains something we don't track
				 *  --> abort..
				 */
				return argumentEqNode;
			}
			arguments.add(argumentEqNode);
			mArrayToAccessingEqNodes.addPair(arrayId, argumentEqNode);
		}

		result = getOrConstructEqFnNode(arrayId, arguments);
		mTermToEqNode.put(mds.getSelectTerm(), result);
		return result;
	}

	private static boolean isAtomicTerm(final Term t) {
		return t instanceof TermVariable || t instanceof ConstantTerm
				|| (t instanceof ApplicationTerm && ((ApplicationTerm) t).getParameters().length == 0);
	}

	private EqNode getOrConstructEqNode(final Term t) {
		EqNode result = mTermToEqNode.get(t);
		if (result != null) {
			return result;
		}
		// we need to construct a fresh EqNode
		if (isAtomicTerm(t)) {
			result = getOrConstructEqBaseNode(t);
			return result;
		}
		// we need to construct an EqFunctionNode
		assert t instanceof ApplicationTerm;
		final ApplicationTerm at = (ApplicationTerm) t;
		if (at.getFunction().getName() == "select") {
			final MultiDimensionalSelect mds = new MultiDimensionalSelect(at);
			return constructEqNode(mds);
		} else if (at.getFunction().getName() == "store") {
			final MultiDimensionalStore mds = new MultiDimensionalStore(at);
			return constructEqNode(mds);
		} else {
			/*
			 * We have a non-atomic array index (like i + 5).
			 */
			return getOrConstructNonAtomicEqBaseNode(t);
		}
	}

	private EqNode getOrConstructNonAtomicEqBaseNode(Term t) {

		Set<EqAtomicBaseNode> constituentNodes = new HashSet<>();
		boolean global = true;
		for (TermVariable fv : t.getFreeVars()) {
			EqAtomicBaseNode node = getOrConstructEqBaseNode(fv);
			global &= node.isGlobal();
			constituentNodes.add(node);
		}
		EqNonAtomicBaseNode result = new EqNonAtomicBaseNode(t, global);
		for (EqAtomicBaseNode node : constituentNodes) {
			node.addDependentNonAtomicBaseNode(result);
		}
		mTermToEqNode.put(t, result);
		return result;
	}

	/**
	 * either gets the symbol table entry for a given (atomic) term, or constructs a ConstOrLiteral.
	 * 
	 * NOTE that this method may only be called on Terms where the TermVariables have been normalized,
	 *  i.e., replaced with their ProgramVariable's TermVariable
	 * @param t
	 * @return
	 */
	private IProgramVarOrConst getOrConstructBoogieVarOrConst(final Term t) {
		IProgramVarOrConst result = mTermToProgramVarOrConst.get(t);
		if (result != null) {
			return result;
		}

		if (t instanceof ApplicationTerm) {
			assert ((ApplicationTerm) t).getParameters().length == 0 : "not a constant";
			result = mSymboltable.getProgramConst((ApplicationTerm) t);
			if (result == null) {
				result = new ConstOrLiteral((ApplicationTerm) t);
			}
		} else if (t instanceof ConstantTerm) {
			result = new ConstOrLiteral((ConstantTerm) t);
		} else if (t instanceof TermVariable) {
			final IProgramVar pv = mSymboltable.getProgramVar((TermVariable) t);
			assert pv != null : "?";
			result = pv;
		} else {
			assert false;
			return null;
		}
		mTermToProgramVarOrConst.put(t, result);
		assert result != null;
		return result;
	}

	/**
	 *
	 * @param tv
	 * @return
	 */
	private EqAtomicBaseNode getOrConstructEqBaseNode(final Term t) {
		IProgramVarOrConst bv = getOrConstructBoogieVarOrConst(t);
		EqAtomicBaseNode result = mEqBaseNodeStore.get(bv);

		if (result == null) {
			result = new EqAtomicBaseNode(bv);
			mEqBaseNodeStore.put(bv, result);
		}
		mTermToEqNode.put(t, result);
		return result;
	}

	// private EqFunctionNode getOrConstructEqFnNode(final EqNode eqNode, final List<EqNode> indices) {
	//
	// }

	private EqFunctionNode getOrConstructEqFnNode(final IProgramVarOrConst function, final List<EqNode> indices) {

		EqFunctionNode result = mEqFunctionNodeStore.get(function, indices);
		if (result == null) {
			result = new EqFunctionNode(function, indices, mManagedScript);

			mArrayIdToFnNodes.addPair(function, result);

			mEqFunctionNodeStore.put(function, indices, result);
		}

		for (final EqNode child : indices) {
			child.addParent(result);
		}
		return result;
	}

	public HashRelation<IProgramVarOrConst, EqFunctionNode> getArrayIdToFnNodeMap() {
		assert mArrayIdToFnNodes != null;
		return mArrayIdToFnNodes;
	}

	@Override
	public String toString() {
		return "-RCFGArrayIndexCollector-";
	}

	public Map<Term, EqNode> getTermToEqNodeMap() {
		return mTermToEqNode;
	}

	public IProgramVarOrConst getIProgramVarOrConstOrLiteral(final Term term,
			final Map<TermVariable, IProgramVar> tvToPvMap) {
		if (term instanceof TermVariable) {
			final IProgramVar pv = tvToPvMap.get(term);
//			assert mTermToProgramVarOrConst.get(pv.getTerm()) == pv : "right?...";
			return pv;
		}
		return mTermToProgramVarOrConst.get(term);
	}

	/**
	 * @param array
	 * @param index
	 * @return true iff the given array is ever accessed using the given index in the program.
	 */
	public boolean isArrayAccessedAt(final IProgramVarOrConst array, final EqNode index) {
		return mArrayToAccessingEqNodes.containsPair(array, index);
	}
	public Set<EqNode> getAccessingIndicesForArrays(final Set<IProgramVarOrConst> arrays) {
		Set<EqNode> result = new HashSet<>();
		for (IProgramVarOrConst a : arrays) {
			result.addAll(getAccessingIndicesForArray(a));
		}
		return result;
	}
	
	public Set<EqNode> getAccessingIndicesForArray(IProgramVarOrConst array) {
		return Collections.unmodifiableSet(mArrayToAccessingEqNodes.getImage(array));
	}

	/**
	 * Called after the main run (which is initiated by the constructor)
	 *
	 * We have collected all (multi-dimensional) select-terms in the program and all equations. Plan: construct EqNodes
	 * for everything that is equated to a select-term, and then build the transitive closure.
	 */
	public void postProcess() {
		/*
		 * Add to the initial set all terms that are equated to a select-term
		 */
		final Set<Term> termsEquatedWithASelectTerm = new HashSet<>();
		for (final ApplicationTerm eq : mEquations) {
			if (mSelectTerms.contains(eq.getParameters()[0]) && !mSelectTerms.contains(eq.getParameters()[1])) {
				termsEquatedWithASelectTerm.add(eq.getParameters()[1]);
			} else if (mSelectTerms.contains(eq.getParameters()[1]) && !mSelectTerms.contains(eq.getParameters()[0])) {
				termsEquatedWithASelectTerm.add(eq.getParameters()[0]);
			}
		}

		/*
		 * Add to the initial set all terms that are equated to an array index.
		 */
		final Set<Term> arrayIndices = new HashSet<>();
		for (final IProgramVarOrConst array : mArrayToAccessingEqNodes.getDomain()) {
			for (final EqNode eqNode : mArrayToAccessingEqNodes.getImage(array)) {
				arrayIndices.add(eqNode.getTerm());
			}
		}

		/*
		 * compute the closure over the "being-equated-in-the-program" relation
		 */
		final Set<Term> closure = new HashSet<>(termsEquatedWithASelectTerm);
		closure.addAll(arrayIndices);

		boolean madeProgress = true;
		while (madeProgress) {
			madeProgress = false;

			for (final ApplicationTerm eq : mEquations) {
				if (closure.contains(eq.getParameters()[0]) && !closure.contains(eq.getParameters()[1])) {
					closure.add(eq.getParameters()[1]);
					madeProgress = true;
				} else if (closure.contains(eq.getParameters()[1]) && !closure.contains(eq.getParameters()[0])) {
					closure.add(eq.getParameters()[0]);
					madeProgress = true;
				}
			}
		}

		/*
		 * Construct EqNodes for all the additionally discovered Terms
		 */
		for (final Term t : closure) {
			getOrConstructEqNode(t);
		}
		
		mLogger.info("VPDomainPreanalysis finished.");
		mLogger.info("tracked arrays: " + mArrayIdToFnNodes.getDomain());
		mLogger.info("total number of nodes in congruence graph: " + mTermToEqNode.values().size());
	}

	/**
	 *
	 * @param term
	 * @param tvToPvMap
	 * @return the EqNode for term (normalized by tvToPvMap) if we track term, null otherwise
	 */
	public EqNode getEqNode(final Term term, final Map<TermVariable, IProgramVar> tvToPvMap) {
		// our mapping is in terms of normalized terms, so we need to make a substitution before we can look it up
		final Map<Term, Term> substitionMap = VPDomainHelpers.computeNormalizingSubstitution(tvToPvMap);
		final Term termWithNormalizedVariables = new Substitution(mManagedScript, substitionMap).transform(term);
		final EqNode result = mTermToEqNode.get(termWithNormalizedVariables);
		return result;
	}
	
	public EqNode getEqNode(IProgramVarOrConst pvoc) {
		return getEqNode(pvoc.getTerm(), Collections.emptyMap());
	}
	
	public VPDomainPreanalysisSettings getSettings() {
		return mSettings;
	}

	public boolean isArrayTracked(Term arrayid, Map<TermVariable, IProgramVar> tvToPvMap) {
		IProgramVarOrConst pvoc = getIProgramVarOrConstOrLiteral(arrayid, tvToPvMap);
		assert pvoc != null : "perhaps implement this case?";
	    return isArrayTracked(pvoc);
	}

//	public boolean isArrayTracked(Term arrayid, Map<TermVariable, IProgramVar> tvToPvMap) {
	public boolean isArrayTracked(IProgramVarOrConst pvoc) {
		// our mapping is in terms of normalized terms, so we need to make a substitution before we can look it up
//		String normalizedName = arrayid.toString();
//		if (tvToPvMap.containsKey(arrayid)) {
//			normalizedName = tvToPvMap.get(arrayid).toString();
//		}
//		return mSettings.getArraysToTrack().contains(normalizedName);
		return mSettings.getArraysToTrack().contains(pvoc.toString());
	}
	
	public ManagedScript getManagedScript() {
		return mManagedScript;
	}

	public boolean isArrayTracked(Term lhs, Map<IProgramVar, TermVariable> inVars,
			Map<IProgramVar, TermVariable> outVars) {
		return isArrayTracked(lhs, 
				VPDomainHelpers.computeProgramVarMappingFromInVarOutVarMappings(inVars, outVars));
	}

	public ILogger getLogger() {
		return mLogger;
	}

	public boolean isDebugMode() {
		return mIsDebugMode;
	}

	public Benchmark getBenchmark() {
		return mBenchmark;
	}
}

class VPDomainPreanalysisSettings {
	private final Set<String> mArrayNames;

	VPDomainPreanalysisSettings() {
		mArrayNames = new HashSet<>();
		mArrayNames.add(SFO.LENGTH);
		mArrayNames.add(SFO.VALID);
		mArrayNames.add(SFO.MEMORY_INT);
		mArrayNames.add(SFO.MEMORY_POINTER);
		
		
		//TODO restore svcomp settings
		mArrayNames.add("f_a");
		
		Set<String> oldArrayNames = new HashSet<>();
		for (String an : mArrayNames) {
			oldArrayNames.add("old(" + an + ")");
		}
		mArrayNames.addAll(oldArrayNames);
	}
	
	public boolean trackAllArrays() {
		return false;
	}
	
	public Set<String> getArraysToTrack() {
			return mArrayNames;
	}
}

class SFO { //copied from translation TODO: perhaps move it to utils or so..
	/**
	 * The "#length" array identifier.
	 */
	public static final String LENGTH = "#length";
	/**
	 * The "#valid" array identifier.
	 */
	public static final String VALID = "#valid";
	/**
	 * The "#memory" array identifier.
	 */
	public static final String MEMORY = "#memory";
	
	/**
	 * String holding "int".
	 */
	public static final String INT = "int";

	/**
	 * The "$Pointer$" type identifier.
	 */
	public static final String POINTER = "$Pointer$";	

	/**
	 * combined SFOs for memory arrays:
	 */
	public static final String MEMORY_INT = MEMORY + "_" + INT;
//	public static final String MEMORY_REAL = MEMORY + "_" + REAL;
	public static final String MEMORY_POINTER = MEMORY + "_" + POINTER;
	
}