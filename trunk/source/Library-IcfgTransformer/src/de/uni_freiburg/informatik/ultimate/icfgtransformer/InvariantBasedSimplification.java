/*
 * Copyright (C) 2024 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.CopyingTransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgSummaryTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.ExtendedSimplificationResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SubTermFinder;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class InvariantBasedSimplification extends CopyingTransformulaTransformer {

	private final IUltimateServiceProvider mServices;
	private final Map<IcfgLocation, IPredicate> mInvariants;
	private final ManagedScript mMgdScript;
	private long mOverallTreesizeReduction = 0;
	private int mEdges = 0;
	private int mSimplifiedEdges = 0;
	private int mSimplifiedToFalse = 0;

	public InvariantBasedSimplification(final IUltimateServiceProvider services, final ILogger logger,
			final CfgSmtToolkit oldToolkit, final Map<IcfgLocation, IPredicate> invariants) {
		super(logger, oldToolkit.getManagedScript(), oldToolkit);
		mServices = services;
		mMgdScript = oldToolkit.getManagedScript();
		mInvariants = invariants;
	}

	@Override
	public TransformulaTransformationResult transform(final IIcfgTransition<? extends IcfgLocation> oldEdge,
			final UnmodifiableTransFormula tf) {
		mEdges++;
		if (oldEdge instanceof IIcfgInternalTransition) {
			return trySimplification(oldEdge, tf);
		} else if (oldEdge instanceof IIcfgSummaryTransition) {
			if (((IIcfgSummaryTransition) oldEdge).calledProcedureHasImplementation()) {
				// do not simplify
				return new TransformulaTransformationResult(tf);
			} else {
				return trySimplification(oldEdge, tf);
			}
		} else if (oldEdge instanceof IIcfgCallTransition) {
			// do not simplify
			return new TransformulaTransformationResult(tf);
		} else if (oldEdge instanceof IIcfgReturnTransition) {
			// do not simplify
			return new TransformulaTransformationResult(tf);
		} else {
			throw new AssertionError("Unsupported edge " + oldEdge.getClass().getSimpleName());
		}
	}

	public TransformulaTransformationResult trySimplification(final IIcfgTransition<? extends IcfgLocation> oldEdge,
			final UnmodifiableTransFormula tf) throws AssertionError {
		final IcfgLocation src = oldEdge.getSource();
		final IPredicate inv = mInvariants.get(src);
		Objects.requireNonNull(inv);
		final ExtendedSimplificationResult esr = SmtUtils.simplifyWithStatistics(mMgdScript, tf.getFormula(),
				inv.getFormula(), mServices, SimplificationTechnique.SIMPLIFY_DDA2);
		final long reduction = esr.getReductionOfTreeSize();
		if (tf.getFormula() != esr.getSimplifiedTerm()) {
			mSimplifiedEdges++;
			mOverallTreesizeReduction += reduction;
			if (!SmtUtils.isFalseLiteral(tf.getFormula()) && SmtUtils.isFalseLiteral(esr.getSimplifiedTerm())) {
				mSimplifiedToFalse++;
			}
			final UnmodifiableTransFormula newTf = constructSimplifiedTransformula(tf, esr.getSimplifiedTerm());
			return new TransformulaTransformationResult(newTf);
		} else {
			return new TransformulaTransformationResult(tf);
		}
	}

	public UnmodifiableTransFormula constructSimplifiedTransformula(final UnmodifiableTransFormula tf,
			final Term newTerm) {
		final Set<Term> freeVarsInOldTerm = new HashSet<>(Arrays.asList(tf.getFormula().getFreeVars()));
		final Set<Term> freeVarsInNewTerm = new HashSet<>(Arrays.asList(newTerm.getFreeVars()));
		final Map<IProgramVar, TermVariable> newInVars = new HashMap<>(tf.getInVars());
		{
			final Iterator<Entry<IProgramVar, TermVariable>> it = newInVars.entrySet().iterator();
			while (it.hasNext()) {
				final Entry<IProgramVar, TermVariable> entry = it.next();
				if (freeVarsInOldTerm.contains(entry.getValue()) && !freeVarsInNewTerm.contains(entry.getValue())) {
					it.remove();
				}
			}
		}
		final Set<IProgramConst> programConsts;
		if (tf.getNonTheoryConsts().isEmpty()) {
			programConsts = tf.getNonTheoryConsts();
		} else {
			programConsts = new HashSet<>(tf.getNonTheoryConsts());
			final Predicate<Term> p = (x -> (x instanceof ApplicationTerm)
					&& (!((ApplicationTerm) x).getFunction().isIntern()));
			final Set<Term> applicationTerms = SubTermFinder.find(newTerm, p, false);
			final Iterator<IProgramConst> it = programConsts.iterator();
			while (it.hasNext()) {
				final IProgramConst pc = it.next();
				if (!applicationTerms.contains(pc.getDefaultConstant())) {
					it.remove();
				}
			}
		}
		final TransFormulaBuilder tfb = new TransFormulaBuilder(newInVars, tf.getOutVars(), programConsts.isEmpty(),
				programConsts.isEmpty() ? null : tf.getNonTheoryConsts(), tf.getBranchEncoders().isEmpty(),
				tf.getBranchEncoders().isEmpty() ? null : tf.getBranchEncoders(), tf.getAuxVars().isEmpty());
		tfb.setFormula(newTerm);
		tfb.addAuxVarsButRenameToFreshCopies(tf.getAuxVars(), mMgdScript);
		if (SmtUtils.isFalseLiteral(newTerm)) {
			tfb.setInfeasibility(Infeasibility.INFEASIBLE);
		} else {
			if (tf.isInfeasible() == Infeasibility.INFEASIBLE) {
				throw new AssertionError("Infeasible but not false");
			}
			tfb.setInfeasibility(tf.isInfeasible());
		}
		final UnmodifiableTransFormula newTf = tfb.finishConstruction(mMgdScript);
		return newTf;
	}

	public long getOverallTreesizeReduction() {
		return mOverallTreesizeReduction;
	}

	public int getEdges() {
		return mEdges;
	}

	public int getSimplifiedEdges() {
		return mSimplifiedEdges;
	}

	public int getSimplifiedToFalse() {
		return mSimplifiedToFalse;
	}

}
