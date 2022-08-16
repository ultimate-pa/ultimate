/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.TransferrerWithVariableCache;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * An object of this class allows one to construct a {@link UnmodifiableTransFormula}. {@link UnmodifiableTransFormula}s
 * are unmodifiable and have a package-private constructor. This class allows to collect data for a TransFormula and to
 * construct it.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class TransFormulaBuilder {
	private final Map<IProgramVar, TermVariable> mInVars;
	private final Map<IProgramVar, TermVariable> mOutVars;
	private final Set<IProgramConst> mNonTheoryConsts;
	private final Set<TermVariable> mAuxVars;
	private final Set<TermVariable> mBranchEncoders;
	private Infeasibility mInfeasibility = null;
	private Term mFormula = null;
	private boolean mConstructionFinished = false;

	/**
	 * Specify inVars, outVars, auxVars, and branchEncoders that are used initially while constructing a new
	 * {@link UnmodifiableTransFormula}. For each of these arguments we do not use the Map/Set but construct a copy.
	 * Each of these arguments my be null, and if this is the case we start with an empty Map/Set. If emptyAuxVars or
	 * emptyBranchEncoders is "true" we use an emptyMap/emptySet for the respective Map/Set.
	 */
	public TransFormulaBuilder(final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars, final boolean emptyNonTheoryConsts,
			final Set<IProgramConst> nonTheoryConsts, final boolean emptyBranchEncoders,
			final Collection<TermVariable> branchEncoders, final boolean emptyAuxVars) {
		if (inVars == null) {
			mInVars = new HashMap<>();
		} else {
			mInVars = new HashMap<>(inVars);
		}
		if (outVars == null) {
			mOutVars = new HashMap<>();
		} else {
			mOutVars = new HashMap<>(outVars);
		}
		if (emptyNonTheoryConsts) {
			mNonTheoryConsts = ImmutableSet.empty();
			if (nonTheoryConsts != null && !nonTheoryConsts.isEmpty()) {
				throw new IllegalArgumentException("if emptyNonTheoryConsts=true, you cannot provide nonTheoryConsts");
			}
		} else if (nonTheoryConsts == null) {
			mNonTheoryConsts = new HashSet<>();
		} else {
			mNonTheoryConsts = new HashSet<>(nonTheoryConsts);
		}
		if (emptyAuxVars) {
			mAuxVars = ImmutableSet.empty();
		} else {
			mAuxVars = new HashSet<>();
		}
		if (emptyBranchEncoders) {
			mBranchEncoders = ImmutableSet.empty();
			if (branchEncoders != null && !branchEncoders.isEmpty()) {
				throw new IllegalArgumentException("if emptyBranchEncoders=true, you cannot provide branchEncoders");
			}
		} else if (branchEncoders == null) {
			mBranchEncoders = new HashSet<>();
		} else {
			mBranchEncoders = new HashSet<>(branchEncoders);
		}
	}

	public boolean addAuxVar(final TermVariable arg0) {
		if (mConstructionFinished) {
			throw new IllegalStateException("Construction finished, TransFormula must not be modified.");
		}
		return mAuxVars.add(arg0);
	}

	/**
	 * Add a set of aux vars but rename each of them to a fresh constant. Requires that the formula is already set,
	 * since we also have to do the renaming in the formula.
	 *
	 * @param arg0
	 */
	public void addAuxVarsButRenameToFreshCopies(final Set<? extends TermVariable> arg0, final ManagedScript script) {
		if (mConstructionFinished) {
			throw new IllegalStateException("Construction finished, TransFormula must not be modified.");
		}
		if (mFormula == null) {
			throw new IllegalStateException("Formula not yet set, cannot rename.");
		}
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (final TermVariable auxVar : arg0) {
			final TermVariable newAuxVar = script.constructFreshCopy(auxVar);
			addAuxVar(newAuxVar);
			substitutionMapping.put(auxVar, newAuxVar);
		}
		mFormula = Substitution.apply(script, substitutionMapping, mFormula);
	}

	public boolean removeAuxVar(final TermVariable arg0) {
		if (mConstructionFinished) {
			throw new IllegalStateException("Construction finished, TransFormula must not be modified.");
		}
		return mAuxVars.remove(arg0);
	}

	public boolean addBranchEncoder(final TermVariable arg0) {
		if (mConstructionFinished) {
			throw new IllegalStateException("Construction finished, TransFormula must not be modified.");
		}
		return mBranchEncoders.add(arg0);
	}

	public boolean addBranchEncoders(final Collection<? extends TermVariable> arg0) {
		if (mConstructionFinished) {
			throw new IllegalStateException("Construction finished, TransFormula must not be modified.");
		}
		return mBranchEncoders.addAll(arg0);
	}

	public boolean containsInVar(final IProgramVar arg0) {
		return mInVars.containsKey(arg0);
	}

	public TermVariable getInVar(final IProgramVar key) {
		return mInVars.get(key);
	}

	public TermVariable addInVar(final IProgramVar key, final TermVariable value) {
		if (mConstructionFinished) {
			throw new IllegalStateException("Construction finished, TransFormula must not be modified.");
		}
		return mInVars.put(key, value);
	}

	public void addInVars(final Map<? extends IProgramVar, ? extends TermVariable> m) {
		if (mConstructionFinished) {
			throw new IllegalStateException("Construction finished, TransFormula must not be modified.");
		}
		mInVars.putAll(m);
	}

	public TermVariable removeInVar(final IProgramVar key) {
		if (mConstructionFinished) {
			throw new IllegalStateException("Construction finished, TransFormula must not be modified.");
		}
		return mInVars.remove(key);
	}

	public boolean containsOutVar(final IProgramVar arg0) {
		return mOutVars.containsKey(arg0);
	}

	public TermVariable getOutVar(final IProgramVar key) {
		return mOutVars.get(key);
	}

	public TermVariable addOutVar(final IProgramVar key, final TermVariable value) {
		if (mConstructionFinished) {
			throw new IllegalStateException("Construction finished, TransFormula must not be modified.");
		}
		return mOutVars.put(key, value);
	}

	public void addOutVars(final Map<? extends IProgramVar, ? extends TermVariable> m) {
		if (mConstructionFinished) {
			throw new IllegalStateException("Construction finished, TransFormula must not be modified.");
		}
		mOutVars.putAll(m);
	}

	public TermVariable removeOutVar(final IProgramVar key) {
		if (mConstructionFinished) {
			throw new IllegalStateException("Construction finished, TransFormula must not be modified.");
		}
		return mOutVars.remove(key);
	}

	public void clearOutVars() {
		if (mConstructionFinished) {
			throw new IllegalStateException("Construction finished, TransFormula must not be modified.");
		}
		mOutVars.clear();
	}

	/**
	 * Remove from the outVars all local vars and oldVars.
	 */
	public void removeOutVarsOfLocalContext() {
		if (mConstructionFinished) {
			throw new IllegalStateException("Construction finished, TransFormula must not be modified.");
		}
		final Iterator<Entry<IProgramVar, TermVariable>> it = mOutVars.entrySet().iterator();
		while (it.hasNext()) {
			final Entry<IProgramVar, TermVariable> next = it.next();
			if (!next.getKey().isGlobal() || next.getKey().isOldvar()) {
				it.remove();
			}
		}
	}

	public boolean addProgramConst(final IProgramConst progConst) {
		if (mConstructionFinished) {
			throw new IllegalStateException("Construction finished, TransFormula must not be modified.");
		}
		return mNonTheoryConsts.add(progConst);
	}

	public void setInfeasibility(final Infeasibility infeasibility) {
		if (mConstructionFinished) {
			throw new IllegalStateException("Construction finished, TransFormula must not be modified.");
		}
		if (mInfeasibility != null) {
			throw new IllegalStateException("Infeasibility already set.");
		}
		mInfeasibility = infeasibility;
	}

	public void setFormula(final Term formula) {
		if (mConstructionFinished) {
			throw new IllegalStateException("Construction finished, TransFormula must not be modified.");
		}
		if (mFormula != null) {
			throw new IllegalStateException("Formula already set.");
		}
		mFormula = formula;
	}

	/**
	 * Ensures that the constructed TransFormula will be in <em>internal normal form</em>.
	 *
	 * See {@link TransFormulaUtils#hasInternalNormalForm(TransFormula)} for more information. If the caller already
	 * ensures that the TransFormula will be in internal normal form, it is not necessary to call this method.
	 *
	 * This method must only be called after the formula has been set, but before
	 * {@link #finishConstruction(ManagedScript)} has been called. Do not modify the input or output variables after
	 * calling this method.
	 */
	public void ensureInternalNormalForm() {
		if (mFormula == null) {
			throw new IllegalStateException("Cannot ensure internal normal form without formula");
		}
		if (mConstructionFinished) {
			throw new IllegalStateException("Construction finished, TransFormula must not be modified.");
		}

		final List<TermVariable> freeVars = Arrays.asList(mFormula.getFreeVars());
		final Set<IProgramVar> obsoleteInVars = new HashSet<>();
		for (final Map.Entry<IProgramVar, TermVariable> entry : mInVars.entrySet()) {
			if (!mOutVars.containsKey(entry.getKey()) && !freeVars.contains(entry.getValue())) {
				mOutVars.put(entry.getKey(), entry.getValue());
				obsoleteInVars.add(entry.getKey());
			}
		}
		for (final IProgramVar pv : obsoleteInVars) {
			mInVars.remove(pv);
		}
	}

	public UnmodifiableTransFormula finishConstruction(final ManagedScript script) {
		if (mFormula == null) {
			throw new IllegalStateException("cannot finish without formula");
		}
		if (mInfeasibility == null) {
			throw new IllegalStateException("cannot finish without feasibility status");
		}
		mConstructionFinished = true;
		removeSuperfluousVars(mFormula, mInVars, mOutVars, mAuxVars);
		return new UnmodifiableTransFormula(mFormula, Collections.unmodifiableMap(mInVars),
				Collections.unmodifiableMap(mOutVars), ImmutableSet.of(mNonTheoryConsts), ImmutableSet.of(mAuxVars),
				ImmutableSet.of(mBranchEncoders), mInfeasibility, script);
	}

	/**
	 * Remove inVars, outVars and auxVars that are not necessary.
	 * <ul>
	 * <li>Remove auxVars if it does not occur in the formula.</li>
	 * <li>Remove {@link IProgramVar} from inVars and outVars if inVar and outVar are the same but do not occur in the
	 * formula.</li>
	 * <li>Remove {@link IProgramVar} from inVars if it also occurs in outVars, and the inVar does not occur in the
	 * formula.</li>
	 * <li>Remove {@link IProgramVar} from outVars if it also occurs in inVars, and the outVar does not occur in the
	 * formula. However, this can only be done if the inVar is not also removed!</li>
	 * <li>If an {@link IProgramVar} occurs only in the inVars resp. only in the outVars, the variable must be kept
	 * since this indicates the {@link ITransitionRelation} does not state any constraint on the output values resp. the
	 * input values of this variable (sometimes called a havoc). Non-occurring variables implicitly state that the value
	 * of the variable does not change.</li>
	 * </ul>
	 */
	private static void removeSuperfluousVars(final Term formula, final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars, final Set<TermVariable> auxVars) {
		final Set<TermVariable> allVars = new HashSet<>(Arrays.asList(formula.getFreeVars()));
		if (!auxVars.isEmpty()) {
			auxVars.retainAll(allVars);
		}

		final List<IProgramVar> superfluousOutVars = new ArrayList<>();
		for (final Entry<IProgramVar, TermVariable> bv : outVars.entrySet()) {
			final IProgramVar pv = bv.getKey();
			final TermVariable outVar = bv.getValue();
			final TermVariable inVar = inVars.get(pv);

			if (inVar == null) {
				// The variable occurs only as outVar. Thus it may change its value, and we must keep the outVar.
				continue;
			}

			if (inVar == outVar) {
				// The variable pv does not change. If it is not constrained either (because it does not occur in the
				// formula), it can be removed entirely.
				if (!allVars.contains(outVar)) {
					inVars.remove(pv);
					superfluousOutVars.add(pv);
				}
			} else if (!allVars.contains(inVar)) {
				// The variable pv may change, and its input value is not constrained. Hence we can remove it from
				// inVars (but we keep the outVar).
				inVars.remove(pv);
			} else if (!allVars.contains(outVar)) {
				// The variable is havoced. We do not need to keep the outVar, because a variable that occurs only as
				// inVar is still havoced.
				superfluousOutVars.add(pv);
			}
		}
		for (final IProgramVar bv : superfluousOutVars) {
			outVars.remove(bv);
		}
	}

	/**
	 * Construct TransFormula with "true" formula and no variables.
	 */
	public static UnmodifiableTransFormula getTrivialTransFormula(final ManagedScript script) {
		final TransFormulaBuilder tfb = new TransFormulaBuilder(null, null, true, null, true, null, true);
		tfb.setFormula(script.getScript().term("true"));
		tfb.setInfeasibility(Infeasibility.UNPROVEABLE);
		return tfb.finishConstruction(script);
	}

	/**
	 * Construct TransFormula that represents the identity relation restricted to the predicate pred, i.e., if x is the
	 * vector of variables occurring in pred, the result represents a formula φ(x,x') such that the following holds.
	 * <ul>
	 * <li>φ(x,x') implies x=x'
	 * <li>∃x' φ(x,x') is equivalent to pred
	 * </ul>
	 */
	public static UnmodifiableTransFormula constructTransFormulaFromPredicate(final IPredicate pred,
			final ManagedScript script) {
		return constructTransFormulaFromTerm(pred.getFormula(), pred.getVars(), script);
	}

	public static UnmodifiableTransFormula constructTransFormulaFromTerm(final Term term, final Set<IProgramVar> vars,
			final ManagedScript script) {
		final Set<ApplicationTerm> consts = SmtUtils.extractConstants(term, false);
		if (!consts.isEmpty()) {
			throw new UnsupportedOperationException("constants not yet supported");
		}
		final TransFormulaBuilder tfb = new TransFormulaBuilder(null, null, true, null, true, null, true);
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (final IProgramVar bv : vars) {
			final TermVariable freshTv =
					script.constructFreshTermVariable(bv.getGloballyUniqueId(), bv.getTermVariable().getSort());
			substitutionMapping.put(bv.getTermVariable(), freshTv);
			tfb.addInVar(bv, freshTv);
			tfb.addOutVar(bv, freshTv);
		}
		tfb.setFormula(Substitution.apply(script, substitutionMapping, term));
		tfb.setInfeasibility(SmtUtils.isFalseLiteral(term) ? Infeasibility.INFEASIBLE : Infeasibility.NOT_DETERMINED);
		return tfb.finishConstruction(script);
	}

	/**
	 * Given a list of variables lhs_1,...,lhs_n and a list of terms rhs_1,...,rhs_n, construct a {@link TransFormula}
	 * that represents the assignment lhs_1,...,lhs_n := rhs_1,...,rhs_n
	 */
	public static UnmodifiableTransFormula constructAssignment(final List<? extends IProgramVar> lhs,
			final List<Term> rhs, final IIcfgSymbolTable symbolTable, final ManagedScript mgdScript) {
		return constructEquality(lhs, rhs, symbolTable, mgdScript, false);
	}

	/**
	 * Given a list of variables lhs_1,...,lhs_n and a list of terms rhs_1,...,rhs_n, construct a {@link TransFormula}
	 * that represents the assumption lhs_1==rhs_1,...,lhs_n==rhs_n
	 */
	public static UnmodifiableTransFormula constructEqualityAssumption(final List<? extends IProgramVar> lhs,
			final List<Term> rhs, final IIcfgSymbolTable symbolTable, final ManagedScript mgdScript) {
		return constructEquality(lhs, rhs, symbolTable, mgdScript, true);
	}

	private static UnmodifiableTransFormula constructEquality(final List<? extends IProgramVar> lhs,
			final List<Term> rhs, final IIcfgSymbolTable symbolTable, final ManagedScript mgdScript,
			final boolean lhsAreAlsoInVars) {
		if (lhs.size() != rhs.size()) {
			throw new IllegalArgumentException("different number of argument on LHS and RHS");
		}
		final Set<IProgramVar> rhsPvs = new HashSet<>();
		for (int i = 0; i < rhs.size(); i++) {
			final Set<ApplicationTerm> consts = SmtUtils.extractConstants(rhs.get(i), false);
			if (!consts.isEmpty()) {
				throw new UnsupportedOperationException("constants not yet supported");
			}
			final TermVarsProc tvp = TermVarsProc.computeTermVarsProc(rhs.get(i), mgdScript, symbolTable);
			rhsPvs.addAll(tvp.getVars());
		}

		final TransFormulaBuilder tfb = new TransFormulaBuilder(null, null, true, null, true, null, true);
		final Map<Term, Term> substitutionMapping = new HashMap<>();

		for (final IProgramVar pv : rhsPvs) {
			final TermVariable freshTv =
					mgdScript.constructFreshTermVariable(pv.getGloballyUniqueId(), pv.getTermVariable().getSort());
			substitutionMapping.put(pv.getTermVariable(), freshTv);
			tfb.addInVar(pv, freshTv);
			// outVar may be replaced later
			tfb.addOutVar(pv, freshTv);
		}
		final List<Term> rhsRenamed = rhs.stream().map(x -> Substitution.apply(mgdScript, substitutionMapping, x))
				.collect(Collectors.toList());

		final List<Term> conjuncts = new ArrayList<>();
		for (int i = 0; i < lhs.size(); i++) {
			final IProgramVar pv = lhs.get(i);
			TermVariable outVar = tfb.getOutVar(pv);
			if (outVar == null || !lhsAreAlsoInVars) {
				// create new variable if we do not yet have an outVar for pv
				// or if the outVar should be different from the inVar
				outVar = mgdScript.constructFreshTermVariable(pv.getGloballyUniqueId(), pv.getTermVariable().getSort());
				tfb.addOutVar(pv, outVar);
				if (lhsAreAlsoInVars) {
					// if inVar and outVar should be similar, we entered the outer "if" only because
					// there was not outVar yet, in this case we also have to add the inVar
					tfb.addInVar(pv, outVar);
				}
			}
			conjuncts.add(SmtUtils.binaryEquality(mgdScript.getScript(), outVar, rhsRenamed.get(i)));
		}

		final Term conjunction = SmtUtils.and(mgdScript.getScript(), conjuncts);
		tfb.setFormula(conjunction);
		// an assignment is always feasible
		tfb.setInfeasibility(Infeasibility.UNPROVEABLE);
		return tfb.finishConstruction(mgdScript);
	}

	/**
	 * Given two list of variables lhs_1,...,lhs_n and rhs_1,...,rhs_n, construct a {@link TransFormula} that represents
	 * the assignment lhs_1,...,lhs_n := rhs_1,...,rhs_n
	 */
	public static UnmodifiableTransFormula constructAssignment(final List<? extends IProgramVar> lhs,
			final List<? extends IProgramVar> rhs, final ManagedScript mgdScript) {
		if (lhs.size() != rhs.size()) {
			throw new IllegalArgumentException("different number of argument on LHS and RHS");
		}

		final TransFormulaBuilder tfb = new TransFormulaBuilder(null, null, true, null, true, null, true);

		final List<Term> conjuncts = new ArrayList<>();
		for (int i = 0; i < lhs.size(); i++) {
			final IProgramVar l = lhs.get(i);
			final IProgramVar r = rhs.get(i);
			final TermVariable lFreshTv =
					mgdScript.constructFreshTermVariable(l.getGloballyUniqueId(), l.getTermVariable().getSort());
			final TermVariable rFreshTv =
					mgdScript.constructFreshTermVariable(r.getGloballyUniqueId(), r.getTermVariable().getSort());
			tfb.addInVar(r, rFreshTv);
			if (tfb.getOutVar(r) == null) {
				tfb.addOutVar(r, rFreshTv);
			}
			tfb.addOutVar(l, lFreshTv);
			conjuncts.add(SmtUtils.binaryEquality(mgdScript.getScript(), lFreshTv, rFreshTv));
		}

		final Term conjunction = SmtUtils.and(mgdScript.getScript(), conjuncts);
		tfb.setFormula(conjunction);
		// an assignment is always feasible
		tfb.setInfeasibility(Infeasibility.UNPROVEABLE);
		return tfb.finishConstruction(mgdScript);
	}

	/**
	 * Construct copy of a given {@link Transformula} with minor modifications that are specified by the arguments of
	 * this method.
	 *
	 * @param script
	 *            {@link ManagedScript} that was used to construct the {@link Term}s in the input {@link Transformula}
	 * @param tf
	 *            input {@link Transformula}
	 * @param inVarsToRemove
	 *            {@link IProgramVar}s whose inVars are removed in the result. If the inVar instance is not also an
	 *            outVar the {@link TermVariable} becomes an auxVar.
	 * @param outVarsToRemove
	 *            {@link IProgramVar}s whose outVars are removed in the result. If the outVar instance is not also an
	 *            inVar the {@link TermVariable} becomes an auxVar.
	 * @param additionalOutVars
	 *            Map from {@link IProgramVar}s to {@link TermVariable}s that specifies new outVar instances that are
	 *            added. It is only allowed to add outVars for {@link IProgramVar}s that do not have an outVar (at the
	 *            point in time where outVars specified in the preceding parameter have been removed).
	 * @return Copy if the input {@link Transformula} whith modifications specified by the other parameters of this
	 *         method.
	 */
	public static UnmodifiableTransFormula constructCopy(final ManagedScript script, final TransFormula tf,
			final Collection<IProgramVar> inVarsToRemove, final Collection<IProgramVar> outVarsToRemove,
			final Map<IProgramVar, TermVariable> additionalOutVars) {
		Set<TermVariable> branchEncoders;
		if (tf instanceof UnmodifiableTransFormula) {
			branchEncoders = ((UnmodifiableTransFormula) tf).getBranchEncoders();
		} else {
			branchEncoders = ImmutableSet.empty();
		}
		final TransFormulaBuilder tfb = new TransFormulaBuilder(tf.getInVars(), tf.getOutVars(),
				tf.getNonTheoryConsts().isEmpty(), tf.getNonTheoryConsts().isEmpty() ? null : tf.getNonTheoryConsts(),
				branchEncoders.isEmpty(), branchEncoders.isEmpty() ? null : branchEncoders, false);
		final Set<TermVariable> auxVars = new HashSet<>(tf.getAuxVars());
		for (final IProgramVar pv : inVarsToRemove) {
			assert tfb.mInVars.containsKey(pv) : "illegal to remove variable not that is contained";
			final TermVariable inVar = tfb.mInVars.get(pv);
			final TermVariable outVar = tfb.mOutVars.get(pv);
			tfb.mInVars.remove(pv);
			if (inVar != outVar) {
				// inVar does not occurs already as outVar, we have to add inVar
				// to auxVars
				final boolean modified = auxVars.add(inVar);
				assert modified : "similar var already there";
			}
		}
		for (final IProgramVar pv : outVarsToRemove) {
			assert tfb.mOutVars.containsKey(pv) : "illegal to remove variable not that is contained";
			final TermVariable inVar = tfb.mInVars.get(pv);
			final TermVariable outVar = tfb.mOutVars.get(pv);
			tfb.mOutVars.remove(pv);
			if (inVar != outVar) {
				// outVar does not occur already as inVar, we have to add outVar
				// to auxVars
				final boolean modified = auxVars.add(outVar);
				assert modified : "similar var already there";
			}
		}
		for (final Entry<IProgramVar, TermVariable> entry : additionalOutVars.entrySet()) {
			final TermVariable oldValue = tfb.mOutVars.put(entry.getKey(), entry.getValue());
			if (oldValue != null) {
				throw new IllegalArgumentException(
						"Will not add outvar for " + entry.getKey() + " it already  has an outVar");
			}
		}

		final Infeasibility infeasibility;
		if (tf instanceof UnmodifiableTransFormula) {
			infeasibility = ((UnmodifiableTransFormula) tf).isInfeasible();
		} else {
			infeasibility = Infeasibility.NOT_DETERMINED;
		}
		tfb.setFormula(tf.getFormula());
		tfb.setInfeasibility(infeasibility);
		if (!auxVars.isEmpty()) {
			tfb.addAuxVarsButRenameToFreshCopies(auxVars, script);
		}
		return tfb.finishConstruction(script);
	}

	/**
	 * Construct copy of a given {@link Transformula} where {@link IProgramVar}s are replaced according to a given map.
	 */
	public static <E extends IProgramVar> UnmodifiableTransFormula constructCopy(final ManagedScript script,
			final TransFormula tf, final Map<E, E> variableReplacement) {
		Set<TermVariable> branchEncoders;
		if (tf instanceof UnmodifiableTransFormula) {
			branchEncoders = ((UnmodifiableTransFormula) tf).getBranchEncoders();
		} else {
			branchEncoders = ImmutableSet.empty();
		}
		final Set<TermVariable> auxVars = new HashSet<>(tf.getAuxVars());
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		final Map<IProgramVar, TermVariable> newInVars = new HashMap<>();
		for (final Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
			final E replacement = variableReplacement.get(entry.getKey());
			if (replacement != null) {
				final TermVariable inVar = script.constructFreshCopy(replacement.getTermVariable());
				substitutionMapping.put(tf.getInVars().get(entry.getKey()), inVar);
				newInVars.put(replacement, inVar);
			} else {
				newInVars.put(entry.getKey(), entry.getValue());
			}
		}
		final Map<IProgramVar, TermVariable> newOutVars = new HashMap<>();
		for (final Entry<IProgramVar, TermVariable> entry : tf.getOutVars().entrySet()) {
			final E replacement = variableReplacement.get(entry.getKey());
			if (replacement != null) {
				TermVariable outVar;
				if (entry.getValue().equals(tf.getInVars().get(entry.getKey()))) {
					// inVar and outVar are similar
					outVar = newInVars.get(replacement);
				} else {
					outVar = script.constructFreshCopy(replacement.getTermVariable());
					substitutionMapping.put(tf.getOutVars().get(entry.getKey()), outVar);
				}
				newOutVars.put(replacement, outVar);
			} else {
				newOutVars.put(entry.getKey(), entry.getValue());
			}
		}

		final Infeasibility infeasibility;
		if (tf instanceof UnmodifiableTransFormula) {
			infeasibility = ((UnmodifiableTransFormula) tf).isInfeasible();
		} else {
			infeasibility = Infeasibility.NOT_DETERMINED;
		}
		final Term newFormula = Substitution.apply(script, substitutionMapping, tf.getFormula());
		final TransFormulaBuilder tfb = new TransFormulaBuilder(newInVars, newOutVars,
				tf.getNonTheoryConsts().isEmpty(), tf.getNonTheoryConsts().isEmpty() ? null : tf.getNonTheoryConsts(),
				branchEncoders.isEmpty(), branchEncoders.isEmpty() ? null : branchEncoders, false);
		tfb.setFormula(newFormula);
		tfb.setInfeasibility(infeasibility);
		if (!auxVars.isEmpty()) {
			tfb.addAuxVarsButRenameToFreshCopies(auxVars, script);
		}
		return tfb.finishConstruction(script);
	}

	/**
	 *
	 * Construct a copy of a given {@link Transformula} where all parts are replaced by new ones that are known to a new
	 * solver, i.e., rebuild using the provided {@link TermTransferrer} instance.
	 *
	 * Note that if you want to transfer multiple transformulas to the same new solver instance, you have to share the
	 * cache instance between the transfer calls. Also, <code>script</code> must be the script that {@link Term}s are
	 * transferred to, i.e., the new script.
	 */
	public static UnmodifiableTransFormula transferTransformula(final TransferrerWithVariableCache tt,
			final ManagedScript script, final TransFormula tf, final boolean constructFreshVariables) {

		final Set<TermVariable> branchEncoders;
		if (tf instanceof UnmodifiableTransFormula) {
			final Set<TermVariable> oldBranchEncoders = ((UnmodifiableTransFormula) tf).getBranchEncoders();
			branchEncoders = oldBranchEncoders.stream().map(tt::transferTerm).collect(Collectors.toSet());
		} else {
			branchEncoders = ImmutableSet.empty();
		}

		final Map<IProgramVar, TermVariable> newInVars = new HashMap<>();
		for (final Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
			final IProgramVar newPv = tt.transferProgramVar(entry.getKey());
			final TermVariable newTv;
			if (constructFreshVariables) {
				newTv = script.constructFreshTermVariable(newPv.getGloballyUniqueId(), newPv.getSort());
				tt.getTransferrer().getTransferMapping().put(entry.getValue(), newTv);
			} else {
				newTv = tt.transferTerm(entry.getValue());
			}
			newInVars.put(newPv, newTv);
		}
		final Map<IProgramVar, TermVariable> newOutVars = new HashMap<>();
		for (final Entry<IProgramVar, TermVariable> entry : tf.getOutVars().entrySet()) {
			final IProgramVar newPv = tt.transferProgramVar(entry.getKey());

			final TermVariable newTv;
			if (entry.getValue() == tf.getInVars().get(entry.getKey())) {
				//inVar and outVar are similar
				newTv = newInVars.get(newPv);
			} else {
				if (constructFreshVariables) {
					newTv = script.constructFreshTermVariable(newPv.getGloballyUniqueId(), newPv.getSort());
					tt.getTransferrer().getTransferMapping().put(entry.getValue(), newTv);
				} else {
					newTv = tt.transferTerm(entry.getValue());
				}
			}
			newOutVars.put(newPv, newTv);
		}

		final Set<TermVariable> newAuxVars = new HashSet<>();
		for (final TermVariable auxVar : tf.getAuxVars()) {
			final TermVariable newAuxVar = script.constructFreshTermVariable("auxVar",
					tt.getTransferrer().transferSort(auxVar.getSort()));
			tt.getTransferrer().getTransferMapping().put(auxVar, newAuxVar);
			newAuxVars.add(newAuxVar);
		}

		final Infeasibility infeasibility;
		if (tf instanceof UnmodifiableTransFormula) {
			infeasibility = ((UnmodifiableTransFormula) tf).isInfeasible();
		} else {
			infeasibility = Infeasibility.NOT_DETERMINED;
		}
		final Term newFormula = tt.transferTerm(tf.getFormula());
		final Set<IProgramConst> nonTheoryConsts =
				tf.getNonTheoryConsts().stream().map(tt::transferProgramConst).collect(Collectors.toSet());

		final TransFormulaBuilder tfb = new TransFormulaBuilder(newInVars, newOutVars, nonTheoryConsts.isEmpty(),
				nonTheoryConsts.isEmpty() ? null : nonTheoryConsts, branchEncoders.isEmpty(),
				branchEncoders.isEmpty() ? null : branchEncoders, false);
		for (final TermVariable newAuxVar : newAuxVars) {
			tfb.addAuxVar(newAuxVar);
		}
		tfb.setFormula(newFormula);
		tfb.setInfeasibility(infeasibility);

		return tfb.finishConstruction(script);
	}
}
