/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.AffineSubtermNormalizer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.Nnf;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.Nnf.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SPredicate;

/**
 * Specifies properties of a state in a graph representation of a system. These
 * properties are
 * <ul>
 * <li>Name of a location mLocationName</li>
 * <li>Name of a procedure mProcedureName</li>
 * <li>Possible valuations of variables in this state mStateFormulas</li>
 * </ul>
 * 
 * @author heizmann@informatik.uni-freiburg.de
 */

public class HoareAnnotation extends SPredicate {

	//DD: Matthias, do you really want to save only one annotation?
	private static final String KEY = Activator.PLUGIN_ID;
	private static final long serialVersionUID = 72852101509650437L;
	
	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;

	private final Script mScript;
	private final CfgSymbolTable mSymbolTable;
	private final ManagedScript mMgdScript;
	private final PredicateFactory mPredicateFactory;
	private final ModifiableGlobalVariableManager mModifiableGlobals;

	private final Map<Term, Term> mPrecondition2Invariant = new HashMap<Term, Term>();
	private boolean mIsUnknown = false;

	private boolean mFormulaHasBeenComputed = false;
	private Term mClosedFormula;
	private static final boolean s_AvoidImplications = true;
	

	public HoareAnnotation(final ProgramPoint programPoint, final int serialNumber, 
			final CfgSymbolTable symbolTable, final PredicateFactory predicateFactory, 
			final ModifiableGlobalVariableManager modifiableGlobals,
			final ManagedScript mgdScript,
			final Script script,
			final IUltimateServiceProvider services, 
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique) {
		super(programPoint, serialNumber, new String[] { programPoint.getProcedure() }, script.term(
				"true"), new HashSet<IProgramVar>(), null);
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mServices = services;
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mSymbolTable = symbolTable;
		mMgdScript = mgdScript;
		mPredicateFactory = predicateFactory;
		mScript = script;
		mModifiableGlobals = modifiableGlobals;
	}

	/**
	 * The published attributes. Update this and getFieldValue() if you add new
	 * attributes.
	 */
	private final static String[] s_AttribFields = { "ProgramPoint", "StateIsUnknown", "Formula", "Vars",
			"Precondition2InvariantMapping", "Precondition2InvariantMappingAsStrings" };

	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(final String field) {
		if (field == "Precondition2InvariantMapping") {
			return mPrecondition2Invariant;
		} else if (field == "StateIsUnknown") {
			return mIsUnknown;
		} else if (field == "Precondition2InvariantMappingAsStrings") {
			return getPrecondition2InvariantMappingAsStrings();
		} else {
			return super.getFieldValue(field);
		}
	}

	public void addInvariant(final IPredicate procPrecond, final IPredicate locInvar) {
		if (mFormulaHasBeenComputed) {
			throw new UnsupportedOperationException("Once Formula has been"
					+ " computed it is not allowed to add new Formulas");
		}
		if (mPredicateFactory.isDontCare(procPrecond) || mPredicateFactory.isDontCare(locInvar)) {
			mIsUnknown = true;
			return;
		}
		mVars.addAll(procPrecond.getVars());
		mVars.addAll(locInvar.getVars());
		final Term procPrecondFormula = procPrecond.getFormula();
		// procPrecondFormula = (new SimplifyDDA(mScript,
		// s_Logger)).getSimplifiedTerm(procPrecondFormula);
		final Term locInvarFormula = locInvar.getFormula();
		Term invarForPrecond = mPrecondition2Invariant.get(procPrecondFormula);
		if (invarForPrecond == null) {
			invarForPrecond = locInvarFormula;
		} else {
			invarForPrecond = Util.and(mScript, invarForPrecond, locInvarFormula);
		}
		// invarForPrecond = (new SimplifyDDA(mScript,
		// s_Logger)).getSimplifiedTerm(invarForPrecond);
		// procPrecondFormula = (new SimplifyDDA(mScript,
		// s_Logger)).getSimplifiedTerm(procPrecondFormula);
		mPrecondition2Invariant.put(procPrecondFormula, invarForPrecond);
	}

	@Override
	public Term getFormula() {
		if (!mFormulaHasBeenComputed) {
			computeFormula();
			mFormulaHasBeenComputed = true;
		}
		return mFormula;
	}
	
	@Override
	public Term getClosedFormula() {
		if (!mFormulaHasBeenComputed) {
			computeFormula();
			mFormulaHasBeenComputed = true;
		}
		return mClosedFormula;
	}

	private void computeFormula() {
		for (final Term precond : getPrecondition2Invariant().keySet()) {
			Term invariant = getPrecondition2Invariant().get(precond);
			invariant = SmtUtils.simplify(mMgdScript, invariant, mServices, mSimplificationTechnique); 
			Term precondTerm = Util.implies(mScript, precond, invariant);
			if (s_AvoidImplications) {
				precondTerm = (new Nnf(mMgdScript, mServices, QuantifierHandling.KEEP)).transform(precondTerm);
			}
			mLogger.debug("In " + this + " holds " + invariant + " for precond " + precond);
			mFormula = Util.and(mScript, mFormula, precondTerm);
		}
		mFormula = substituteOldVarsOfNonModifiableGlobals(getProgramPoint().getProcedure(), mVars,
				mFormula);
		mFormula = SmtUtils.simplify(mMgdScript, mFormula, mServices, mSimplificationTechnique); 
		mFormula = getPositiveNormalForm(mFormula);
		final TermVarsProc tvp = TermVarsProc.computeTermVarsProc(mFormula, mScript, mSymbolTable);
		mClosedFormula = PredicateUtils.computeClosedFormula(tvp.getFormula(), tvp.getVars(), mScript);
	}
	
	
	/**
	 * For each oldVar in vars that is not modifiable by procedure proc:
	 * substitute the oldVar by the corresponding globalVar in term and remove
	 * the oldvar from vars.
	 */
	public Term substituteOldVarsOfNonModifiableGlobals(final String proc, final Set<IProgramVar> vars, final Term term) {
		final Set<IProgramVar> oldVarsOfmodifiableGlobals = mModifiableGlobals.getOldVarsAssignment(proc)
				.getAssignedVars();
		final List<IProgramVar> replacedOldVars = new ArrayList<IProgramVar>();

		final ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		final ArrayList<Term> replacers = new ArrayList<Term>();

		for (final IProgramVar bv : vars) {
			if (bv instanceof IProgramOldVar) {
				if (!oldVarsOfmodifiableGlobals.contains(bv)) {
					replacees.add(bv.getTermVariable());
					replacers.add((((IProgramOldVar) bv).getNonOldVar()).getTermVariable());
					replacedOldVars.add(bv);
				}
			}
		}

		final TermVariable[] substVars = replacees.toArray(new TermVariable[replacees.size()]);
		final Term[] substValues = replacers.toArray(new Term[replacers.size()]);
		Term result = mScript.let(substVars, substValues, term);
		result = (new FormulaUnLet()).unlet(result);

		for (final IProgramVar bv : replacedOldVars) {
			vars.remove(bv);
			vars.add(((IProgramOldVar) bv).getNonOldVar());
		}
		return result;
	}
	

	private Term getPositiveNormalForm(final Term term) {
		final Script script = mScript;
		final Term result = (new AffineSubtermNormalizer(mScript, mLogger)).transform(term);
		assert (Util.checkSat(script, script.term("distinct", term, result)) != LBool.SAT);
		return result;
	}

	/**
	 * @return the mFormulaMapping
	 */
	public Map<Term, Term> getPrecondition2Invariant() {
		return mPrecondition2Invariant;
	}

	@Override
	public boolean isUnknown() {
		return mIsUnknown;
	}

	public Map<String, String> getPrecondition2InvariantMappingAsStrings() {
		final HashMap<String, String> result = new HashMap<String, String>();
		for (final Entry<Term, Term> entry : mPrecondition2Invariant.entrySet()) {
			result.put(entry.getKey().toStringDirect(), entry.getValue().toStringDirect());
		}
		return result;
	}
	
	public void annotate(final IElement node) {
		if (node instanceof ProgramPoint) {
			annotate((ProgramPoint) node);
		}
	}

	public void annotate(final ProgramPoint node) {
		node.getPayload().getAnnotations().put(KEY, this);
	}

	public static HoareAnnotation getAnnotation(final IElement node) {
		if (node instanceof ProgramPoint) {
			return getAnnotation((ProgramPoint) node);
		}
		return null;
	}

	public static HoareAnnotation getAnnotation(final ProgramPoint node) {
		if (node.hasPayload()) {
			final IPayload payload = node.getPayload();
			if (payload.hasAnnotation()) {
				final IAnnotations annot = payload.getAnnotations().get(KEY);
				if (annot != null) {
					return (HoareAnnotation) annot;
				}
			}
		}
		return null;
	}

}
