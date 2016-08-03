/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.IFreshTermVariableConstructor;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplicationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BuchiPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.HoareAnnotation;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

public class PredicateFactory {

	private final Boogie2SmtSymbolTable mSymbolTable;
	private final Script mScript;
	private final SimplicationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;

	protected int mSerialNumber;

	private static final Set<IProgramVar> EMPTY_VARS = Collections.emptySet();
	private static final String[] NO_PROCEDURE = new String[0];

	private final IUltimateServiceProvider mServices;
	private final IFreshTermVariableConstructor mFreshVariableConstructor;
	private final ILogger mLogger;
	
	protected Term mDontCareTerm;
	protected Term mEmptyStackTerm;
	
	
	
	public Term getDontCareTerm() {
		return mDontCareTerm;
	}

	public PredicateFactory(final IUltimateServiceProvider services, final Boogie2SMT boogie2smt, final SimplicationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mDontCareTerm = new AuxilliaryTerm("don't care");
		mEmptyStackTerm = new AuxilliaryTerm("emptyStack");
		mSymbolTable = boogie2smt.getBoogie2SmtSymbolTable();
		mFreshVariableConstructor = boogie2smt.getVariableManager();
		mScript = boogie2smt.getScript();
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
	}
	
	/**
	 * Returns true iff each free variables corresponds to a BoogieVar or will
	 * be quantified. Throws an Exception otherwise.
	 */
	private boolean checkIfValidPredicate(final Term term, final Set<TermVariable> quantifiedVariables) {
		for (final TermVariable tv : term.getFreeVars()) {
			final IProgramVar bv = mSymbolTable.getBoogieVar(tv);
			if (bv == null) {
				if (!quantifiedVariables.contains(tv)) {
					throw new AssertionError("Variable " + tv + " does not corresponds to a BoogieVar, and is"
							+ " not quantified, hence this formula cannot" + " define a predicate: " + term);
				}
			}
		}
		return true;
	}

	public static HoareAnnotation getHoareAnnotation(final ProgramPoint programPoint) {
		return HoareAnnotation.getAnnotation(programPoint);
	}

	public PredicateWithHistory newPredicateWithHistory(final ProgramPoint pp, final Term term, final Map<Integer, Term> history) {
		final TermVarsProc tvp = constructTermVarsProc(term);
		final PredicateWithHistory pred = new PredicateWithHistory(pp, mSerialNumber++, tvp.getProcedures(), tvp.getFormula(), tvp.getVars(),
				tvp.getClosedFormula(), history);
		return pred;
	}

	public boolean isDontCare(final IPredicate pred) {
		return pred.getFormula() == mDontCareTerm;
	}
	
	public boolean isDontCare(final Term term) {
		return term == mDontCareTerm;
	}

	public SPredicate newSPredicate(final ProgramPoint pp, final Term term) {
		final TermVarsProc termVarsProc = constructTermVarsProc(term);
		return newSPredicate(pp, termVarsProc);
	}
	
	private SPredicate newSPredicate(final ProgramPoint pp, final TermVarsProc termVarsProc) {
		final SPredicate pred = new SPredicate(pp, mSerialNumber++, termVarsProc.getProcedures(), termVarsProc.getFormula(),
				termVarsProc.getVars(), termVarsProc.getClosedFormula());
		return pred;
	}

	public BasicPredicate newPredicate(final Term term) {
		final TermVarsProc termVarsProc = constructTermVarsProc(term);
		final BasicPredicate predicate = new BasicPredicate(mSerialNumber++, termVarsProc.getProcedures(),
				termVarsProc.getFormula(), termVarsProc.getVars(), termVarsProc.getClosedFormula());
		return predicate;
	}

	private TermVarsProc constructTermVarsProc(final Term term) {
		final TermVarsProc termVarsProc;
		if (term == mDontCareTerm) {
			termVarsProc = constructDontCare();
		} else {
			termVarsProc = TermVarsProc.computeTermVarsProc(term, mScript, mSymbolTable);
		}
		return termVarsProc;
	}

	public MLPredicate newMLPredicate(final ProgramPoint[] programPoints, final Term term) {
		final TermVarsProc termVarsProc = constructTermVarsProc(term);
		final MLPredicate predicate = new MLPredicate(programPoints, mSerialNumber++, termVarsProc.getProcedures(),
				termVarsProc.getFormula(), termVarsProc.getVars(), termVarsProc.getClosedFormula());
		return predicate;
	}
	
	public ProdState getNewProdState(final List<IPredicate> programPoints) {
		return new ProdState(mSerialNumber++, programPoints, mScript.term("true"),new HashSet<IProgramVar>(0));
	}
	
	private TermVarsProc constructDontCare() {
		return new TermVarsProc(mDontCareTerm, EMPTY_VARS, NO_PROCEDURE, mDontCareTerm);
	}

	
	

	public UnknownState newDontCarePredicate(final ProgramPoint pp) {
		final UnknownState pred = new UnknownState(pp, mSerialNumber++, mDontCareTerm);
		return pred;
	}

	public DebugPredicate newDebugPredicate(final String debugMessage) {
		final DebugPredicate pred = new DebugPredicate(debugMessage, mSerialNumber++, mDontCareTerm);
		return pred;
	}

	public ISLPredicate newEmptyStackPredicate() {
		final ProgramPoint pp = new ProgramPoint("noCaller", "noCaller", false, null);
		return newSPredicate(pp, new TermVarsProc(mEmptyStackTerm, EMPTY_VARS, NO_PROCEDURE, mEmptyStackTerm));

	}

	public SPredicate newTrueSLPredicateWithWitnessNode(final ProgramPoint pp, final WitnessNode witnessNode, final Integer stutteringSteps) {
		final SPredicate pred = new SPredicateWithWitnessNode(pp, mSerialNumber++, NO_PROCEDURE, mScript.term("true"), EMPTY_VARS,
				mScript.term("true"), witnessNode, stutteringSteps);
		return pred;
	}

	public HoareAnnotation getNewHoareAnnotation(final ProgramPoint pp, final ModifiableGlobalVariableManager modifiableGlobals) {
		return new HoareAnnotation(pp, mSerialNumber++, mSymbolTable, this, modifiableGlobals, mFreshVariableConstructor, mScript, mServices, mSimplificationTechnique, mXnfConversionTechnique);
	}

	public IPredicate newBuchiPredicate(final Set<IPredicate> inputPreds) {
		final Term conjunction = and(inputPreds);
		final TermVarsProc tvp = TermVarsProc.computeTermVarsProc(conjunction, mScript, mSymbolTable);
		final BuchiPredicate buchi = new BuchiPredicate(mSerialNumber++, tvp.getProcedures(), tvp.getFormula(),
				tvp.getVars(), tvp.getClosedFormula(), inputPreds);
		return buchi;
	}
	
	
	
	public Term and(final IPredicate... preds) {
		return and(Arrays.asList(preds));
	}
	
	public Term and(final Collection<IPredicate> preds) {
		Term term = mScript.term("true");
		for (final IPredicate p : preds) {
			if (isDontCare(p)) {
				return mDontCareTerm;
			}
			term = Util.and(mScript, term, p.getFormula());
		}
		return term;
	}
	
	public Term or(final boolean withSimplifyDDA, final IPredicate... preds) {
		return or(withSimplifyDDA, Arrays.asList(preds));
	}

	public Term or(final boolean withSimplifyDDA, final Collection<IPredicate> preds) {
		Term term = mScript.term("false");
		for (final IPredicate p : preds) {
			if (isDontCare(p)) {
				return mDontCareTerm;
			}
			term = Util.or(mScript, term, p.getFormula());
		}
		if (withSimplifyDDA) {
			term = SmtUtils.simplify(mScript, term, mServices, mSimplificationTechnique, mFreshVariableConstructor);
		}
		return term;
	}

	public Term not(final IPredicate p) {
		if (isDontCare(p)) {
			return mDontCareTerm;
		}
		final Term term = SmtUtils.not(mScript, p.getFormula());
		return term;
	}
	

	

	
	private class AuxilliaryTerm extends Term {

		String mName;

		private AuxilliaryTerm(final String name) {
			super(0);
			mName = name;
		}

		@Override
		public Sort getSort() {
			throw new UnsupportedOperationException("Auxiliary term has no sort");
		}

		@Override
		public void toStringHelper(final ArrayDeque<Object> mTodo) {
			throw new UnsupportedOperationException("Auxiliary term must not be subterm of other terms");
		}

		@Override
		public TermVariable[] getFreeVars() {
			throw new UnsupportedOperationException("Auxiliary term has no vars");
		}

		@Override
		public Theory getTheory() {
			throw new UnsupportedOperationException("Auxiliary term has no theory");
		}

		@Override
		public String toString() {
			return mName;
		}

		@Override
		public String toStringDirect() {
			return mName;
		}

		@Override
		public int hashCode() {
			throw new UnsupportedOperationException("Auxiliary term must not be contained in any collection");
		}
	}


}
