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
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqFunctionNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNodeAndFunctionFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.statistics.Benchmark;

/**
 * Create and collects @EqNode from ApplicationTerm (store and select)
 *
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 * @author Alexander Nutz
 */
public class VPDomainPreanalysis {
	
	
	private final Benchmark mBenchmark;

	private final Map<Term, IProgramVarOrConst> mTermToProgramVarOrConst = new HashMap<>();
	private final ManagedScript mManagedScript;
	private final IIcfgSymbolTable mSymboltable;
	private final Set<ApplicationTerm> mEquations = new HashSet<>();
	private final Set<ApplicationTerm> mSelectTerms = new HashSet<>();
	private final VPDomainPreanalysisSettings mSettings;
	/**
	 * Stores for each array, which Terms(EqNodes) are used to access it.
	 */
	private final HashRelation<IProgramVarOrConst, EqNode> mArrayToAccessingEqNodes = new HashRelation<>();

	/**
	 * Stores for each array, which EqFunctionNodes have it as their topmost function symbol.
	 */
	private final HashRelation<IProgramVarOrConst, EqFunctionNode> mArrayIdToFnNodes = new HashRelation<>();

	private final ILogger mLogger;

	private final boolean mIsDebugMode = true;

	private final EqNodeAndFunctionFactory mEqNodeAndFunctionFactory;

	private final IUltimateServiceProvider mServices;

	private final CfgSmtToolkit mCfgSmtToolkit;

	public VPDomainPreanalysis(final IIcfg<?> root, final ILogger logger, IUltimateServiceProvider services) {
		mManagedScript = root.getCfgSmtToolkit().getManagedScript();
		mLogger = logger;
		mSymboltable = root.getCfgSmtToolkit().getSymbolTable();
		mCfgSmtToolkit = root.getCfgSmtToolkit();
		mSettings = new VPDomainPreanalysisSettings();
		mEqNodeAndFunctionFactory = new EqNodeAndFunctionFactory(this, mManagedScript);
		mServices = services;

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
		final Term formulaWithNormalizedVariables = new Substitution(mManagedScript, substitionMap)
				.transform(tf.getFormula());
		
		/*
		 * handle selects in the formula
		 */
		final List<MultiDimensionalSelect> mdSelectsAll =
				MultiDimensionalSelect.extractSelectDeep(formulaWithNormalizedVariables, false);
		final List<MultiDimensionalSelect> mdSelectsFiltered = null;
//				mSettings.trackAllArrays() ?
//						mdSelectsAll :
//							mdSelectsAll.stream()
//							.filter(mds -> isArrayTracked(
//									getOrConstructBoogieVarOrConst(
//											VPDomainHelpers.getArrayTerm(mds.getArray()))))
//							.collect(Collectors.toList());
//		for (final MultiDimensionalSelect mds : mdSelectsFiltered) {
//			constructEqNode(mds);
//		}

		/*
		 * handle stores in the formula
		 */
		final List<MultiDimensionalStore> mdStoresAll =
				MultiDimensionalStore.extractArrayStoresDeep(formulaWithNormalizedVariables);
		final List<MultiDimensionalStore> mdStoresFiltered = null;
//				mSettings.trackAllArrays() ?
//						mdStoresAll :
//							mdStoresAll.stream()
//							.filter(mds -> isArrayTracked(getOrConstructBoogieVarOrConst(
//									VPDomainHelpers.getArrayTerm(mds.getArray()))))
//							.collect(Collectors.toList());
//		for (final MultiDimensionalStore mds : mdStoresFiltered) {
//			constructEqNode(mds);
//		}

		/*
		 * Store all select-terms and equations for postprocessing
		 *
		 */
//		final Set<String> equationFunctionNames = new HashSet<>(2);
//		equationFunctionNames.add("=");
//		equationFunctionNames.add("distinct");
//		final Set<ApplicationTerm> equations = new ApplicationTermFinder(equationFunctionNames, false)
//				.findMatchingSubterms(formulaWithNormalizedVariables);
//		mEquations.addAll(equations);
//		final Set<ApplicationTerm> selectTerms =
//				mdSelectsFiltered.stream().map(mds -> mds.getSelectTerm()).collect(Collectors.toSet());
//		mSelectTerms.addAll(selectTerms);

	}

	@Override
	public String toString() {
		return "-VPDomainPreanalysis-";
	}

	public Set<EqNode> getAccessingIndicesForArrays(final Set<IProgramVarOrConst> arrays) {
		Set<EqNode> result = new HashSet<>();
		for (IProgramVarOrConst a : arrays) {
			result.addAll(getAccessingIndicesForArray(a));
		}
		return result;
	}
	
	private Set<EqNode> getAccessingIndicesForArray(IProgramVarOrConst array) {
		return Collections.unmodifiableSet(mArrayToAccessingEqNodes.getImage(array));
	}
	
	/**
	 * Called after the main run (which is initiated by the constructor)
	 *
	 * We have collected all (multi-dimensional) select-terms in the program and all equations. 
	 *  Step 1: construct EqNodes for everything that is equated to a select-term, and then build the transitive 
	 *    closure.
	 *  Step 2: build nodes necessary for array equations (i.e., when a and b are equated they should have analogous  
	 *   node sets)
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
//			getOrConstructEqNode(t); TODO
		}
		
		
//		/*
//		 * Say the program equates two arrays, with or without stores in between. Then we want to have the same 
//		 * EqFunctionNodes for these symbols. 
//		 * 
//		 * E.g.
//		 *  We have (= a b), or (= a (store b i x)). Then for every node a[t] we also want to have the node b[t], and
//		 *  vice versa. Note that this introduces EqNode that do not correspond to any term in the formula.
//		 *  Why do we want those extra nodes?
//		 *  
//		 *  say we have a state where
//		 *   valid[p] == 1
//		 *  then we say
//		 *   valid' := valid
//		 *   assume valid'[m] == 0
//		 *  and we want to conclude 
//		 *   m != p
//		 *   Then we can conclude this from valid'[m] != valid'[p], but that we know from the fact that 
//		 *    valid'[p] == valid[p] (and valid[p] == 1 and 1 != 0 and valid'[m] == 0)
//		 *   However our program contains no term that triggers tracking of valid'[p] 
//		 */
//		final Set<ApplicationTerm> arrayEquations = mEquations.stream()
//				.filter(eq -> eq.getFunction().getParameterSorts()[0].isArraySort())
//				.collect(Collectors.toSet());
//		for (ApplicationTerm arrayEquation : arrayEquations) {
//			final Term arg1 = arrayEquation.getParameters()[0];
//			final Term arg2 = arrayEquation.getParameters()[1];
//
//			final EqFunction array1 = mEqNodeAndFunctionFactory.getOrConstructEqFunction(
//					getOrConstructBoogieVarOrConst(VPDomainHelpers.getArrayTerm(arg1)));
//			final EqFunction array2 = mEqNodeAndFunctionFactory.getOrConstructEqFunction(
//					getOrConstructBoogieVarOrConst(VPDomainHelpers.getArrayTerm(arg2)));
//			
//			/*
//			 * for each EqFunctionNode of the form array1[i1 .. in] create the node array2[i1 .. in] and vice versa
//			 */
//			for (EqFunctionNode eqfn : mArrayIdToFnNodes.getImage(array1.getPvoc())) {
//				getOrConstructEqFnNode(array2, eqfn.getArgs());
//			}
//			for (EqFunctionNode eqfn : mArrayIdToFnNodes.getImage(array2.getPvoc())) {
//				getOrConstructEqFnNode(array1, eqfn.getArgs());
//			}
//		}
		
		mLogger.info("VPDomainPreanalysis finished.");
		mLogger.info("tracked arrays: " + mArrayIdToFnNodes.getDomain());
	}


	public VPDomainPreanalysisSettings getSettings() {
		return mSettings;
	}

	public boolean isArrayTracked(Term arrayid, TransFormula tf) {
		return isArrayTracked(arrayid, VPDomainHelpers.computeProgramVarMappingFromTransFormula(tf));
	}

	public boolean isArrayTracked(Term arrayid, Map<TermVariable, IProgramVar> tvToPvMap) {
		if (arrayid instanceof ApplicationTerm && "store".equals(((ApplicationTerm) arrayid).getFunction().getName())) {
			final ApplicationTerm at = (ApplicationTerm) arrayid;
			boolean result = true;
			result &= isArrayTracked(at.getParameters()[0], tvToPvMap);
			result &= isElementTracked(at.getParameters()[1], tvToPvMap);
			result &= isElementTracked(at.getParameters()[2], tvToPvMap);
			return result;
		} else {
			IProgramVarOrConst pvoc = null; //getIProgramVarOrConstOrLiteral(arrayid, tvToPvMap); TODO
//			assert pvoc != null : "perhaps implement this case?";
			return isArrayTracked(pvoc);
		}
	}

	public boolean isArrayTracked(IProgramVarOrConst pvoc) {
	
		if (mSettings.trackAllArrays()) {
			return true;
		}
		
		for (String arrayName : mSettings.getArraysToTrack()) {
			if (pvoc.toString().contains(arrayName)) {
				return true;
			}
		}
		return false;
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
	
	public IIcfgSymbolTable getSymbolTable() {
		return mSymboltable;
	}

	private boolean isElementTracked(Term term, Map<TermVariable, IProgramVar> tvToPvMap) {
		if (mSettings.trackAllElements()) {
			return true;
		}
		final Term normalizedTerm = 
				new Substitution(mManagedScript, VPDomainHelpers.computeNormalizingSubstitution(tvToPvMap))
				.transform(term);
		return false; //getEqNode(normalizedTerm) != null; TODO

	}

	public boolean isElementTracked(Term term, TransFormula tf) {
		return isElementTracked(term, VPDomainHelpers.computeProgramVarMappingFromInVarOutVarMappings(
				tf.getInVars(), tf.getOutVars()));
	}

	public IUltimateServiceProvider getServices() {
		return mServices;
	}

	public IIcfgSymbolTable getSymboltable() {
		return mSymboltable;
	}

	public CfgSmtToolkit getCfgSmtToolkit() {
		return mCfgSmtToolkit;
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
	
	public boolean trackAllElements() {
		return true;
	}
	
	public boolean trackAllArrays() {
		return true;
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