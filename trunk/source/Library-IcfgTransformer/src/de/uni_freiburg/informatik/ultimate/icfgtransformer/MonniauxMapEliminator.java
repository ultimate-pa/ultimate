/*
 * Copyright (C) 2018 Luca Bruder (luca.bruder@gmx.de)
 * Copyright (C) 2018 Lisa Kleinlein (lisa.kleinlein@web.de)
 *
 * This file is part of the ULTIMATE Library-ModelCheckerUtils library.
 *
 * The ULTIMATE Library-ModelCheckerUtils library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by the Free Software Foundation,
 * either version 3 of the License, or (at your option) any later version.
 *
 * The ULTIMATE Library-ModelCheckerUtils library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-ModelCheckerUtils library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-ModelCheckerUtils library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-ModelCheckerUtils library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.IdentityTransformer;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SubstitutionWithLocalSimplification;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * @author Luca Bruder (luca.bruder@gmx.de)
 * @author Lisa Kleinlein (lisa.kleinlein@web.de)
 */
public class MonniauxMapEliminator implements IIcfgTransformer<IcfgLocation> {

	private final ManagedScript mMgdScript;
	private final IIcfg<IcfgLocation> mIcfg;
	private final IIcfg<IcfgLocation> mResultIcfg;
	private final ILogger mLogger;
	private final IBacktranslationTracker mBacktranslationTracker;

	public MonniauxMapEliminator(final ILogger logger, final IIcfg<IcfgLocation> icfg,
			final IBacktranslationTracker backtranslationTracker) {
		mIcfg = Objects.requireNonNull(icfg);
		mMgdScript = mIcfg.getCfgSmtToolkit().getManagedScript();
		mLogger = logger;
		mBacktranslationTracker = backtranslationTracker;
		mResultIcfg = eliminateMaps();
	}

	@Override
	public IIcfg<IcfgLocation> getResult() {
		return mResultIcfg;
	}

	private IIcfg<IcfgLocation> eliminateMaps() {

		final BasicIcfg<IcfgLocation> resultIcfg =
				new BasicIcfg<>(mIcfg.getIdentifier() + "ME", mIcfg.getCfgSmtToolkit(), IcfgLocation.class);
		final ILocationFactory<IcfgLocation, IcfgLocation> funLocFac = (oldLocation, debugIdentifier, procedure) -> {
			final IcfgLocation rtr = new IcfgLocation(debugIdentifier, procedure);
			ModelUtils.copyAnnotations(oldLocation, rtr);
			return rtr;
		};

		final TransformedIcfgBuilder<?, IcfgLocation> lst = new TransformedIcfgBuilder<>(mLogger, funLocFac,
				mBacktranslationTracker, new IdentityTransformer(mIcfg.getCfgSmtToolkit()), mIcfg, resultIcfg);
		iterate(lst);
		lst.finish();
		return resultIcfg;
	}

	private void iterate(final TransformedIcfgBuilder<?, IcfgLocation> lst) {
		final IcfgEdgeIterator iter = new IcfgEdgeIterator(mIcfg);
		final Script script = mMgdScript.getScript();
		while (iter.hasNext()) {
			final IIcfgTransition<?> transition = iter.next();

			int step = 0;

			final int index = 0;

			if (transition instanceof IIcfgInternalTransition) {

				final IIcfgInternalTransition<?> internalTransition = (IIcfgInternalTransition<?>) transition;
				UnmodifiableTransFormula tf = internalTransition.getTransformula();
				Term tfTerm = tf.getFormula();
				// keep or modify tf
				final StoreSelectCollector ssc = new StoreSelectCollector();
				ssc.transform(tfTerm);
				final Map<Term, Term> subst = new HashMap<>();

				for (final Term selectTerm : ssc.mSelectTerms) {
					final ApplicationTerm aterm = (ApplicationTerm) selectTerm;
					final Term[] xy = aterm.getParameters();
					final Term x = xy[0];
					final Term y = xy[1];

					// Stringcreation for variable names
					final String a_step_i = "a_step_i".replace("step", Integer.toString(step));
					a_step_i.replace("i", Integer.toString(index));
					final String i_step = "i_step".replace("step", Integer.toString(step));
					final String x_i = "x_i".replace("i", Integer.toString(index));

					// Creation of variables to be put into the new transformula
					final TermVariable varA =
							mMgdScript.constructFreshTermVariable("a", SmtSortUtils.getIntSort(script));
					final TermVariable i_step_var =
							mMgdScript.constructFreshTermVariable(i_step, SmtSortUtils.getIntSort(script));
					final TermVariable x_i_var =
							mMgdScript.constructFreshTermVariable(x_i, SmtSortUtils.getIntSort(script));
					final Term replacementVariable =
							mMgdScript.constructFreshTermVariable(a_step_i, SmtSortUtils.getIntSort(script));

					final Term replacement = SmtUtils.and(script,
							SmtUtils.implies(script, SmtUtils.binaryEquality(script, y, i_step_var),
									SmtUtils.binaryEquality(script, replacementVariable, x_i_var)));

					subst.put(selectTerm, replacementVariable);
					final Term exprTerm = new SubstitutionWithLocalSimplification(mMgdScript, subst).transform(tfTerm);
					tfTerm = SmtUtils.and(script, SmtUtils.and(script, exprTerm, replacement), script.term("true"));

					final Collection<IProgramVar> inVarsToRemove = null;
					final Collection<IProgramVar> outVarsToRemove = null;
					final HashMap<IProgramVar, TermVariable> additionalOutVars = null;
					// additionalOutVars.put(varA, replacementVariable);

					tf = TransFormulaBuilder.constructCopy(mMgdScript, tf, inVarsToRemove, outVarsToRemove,
							additionalOutVars);

					step++;
				}
				for (final Term storeTerm : ssc.mStoreTerms) {
					// To be implemented step++;
				}
			} else {
				throw new UnsupportedOperationException("not yet implemented");
			}
		}

		// TODO: Create new transition (maybe substitute the formula in tf with tfTerm?)

	}

	// _______________________________________________________________________

	/*
	 * if(transition instanceof IIcfgInternalTransition)
	 *
	 * { final IIcfgInternalTransition<?> internalTransition = (IIcfgInternalTransition<?>) transition; final
	 * UnmodifiableTransFormula tf2 = internalTransition.getTransformula(); final Term tfTerm = tf2.getFormula(); //
	 * keep or modify tf final StoreSelectCollector ssc = new StoreSelectCollector(); ssc.transform(tfTerm); final
	 * Map<Term, Term> subst = new HashMap<>();
	 *
	 * for (final Term selectTerm : ssc.mSelectTerms) { mLogger.info(selectTerm); final TermVariable varA =
	 * mMgdScript.constructFreshTermVariable("a", SmtSortUtils.getIntSort(script)); final Term replacement = null;
	 * subst.put(selectTerm, replacement); final Term exprTerm = new SubstitutionWithLocalSimplification(mMgdScript,
	 * subst).transform(tfTerm); final Term newTerm = SmtUtils.and(script, exprTerm, script.term("true")); } }else {
	 * throw new UnsupportedOperationException("not yet implemented"); }
	 */

	private UnmodifiableTransFormula buildTransitionFormula(final UnmodifiableTransFormula oldFormula,
			final Term newTfFormula, final Map<IProgramVar, TermVariable> inVars,
			final Map<IProgramVar, TermVariable> outVars, final Collection<TermVariable> auxVars) {
		final Set<IProgramConst> nonTheoryConsts = oldFormula.getNonTheoryConsts();
		final boolean emptyAuxVars = auxVars.isEmpty();
		final Collection<TermVariable> branchEncoders = oldFormula.getBranchEncoders();
		final boolean emptyBranchEncoders = branchEncoders.isEmpty();
		final boolean emptyNonTheoryConsts = nonTheoryConsts.isEmpty();
		final TransFormulaBuilder tfb = new TransFormulaBuilder(inVars, outVars, emptyNonTheoryConsts, nonTheoryConsts,
				emptyBranchEncoders, branchEncoders, emptyAuxVars);

		tfb.setFormula(newTfFormula);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		auxVars.stream().forEach(tfb::addAuxVar);
		return tfb.finishConstruction(mMgdScript);
	}

	private final class StoreSelectCollector extends TermTransformer {

		private final Set<Term> mStoreTerms = new HashSet<>();
		private final Set<Term> mSelectTerms = new HashSet<>();

		@Override
		protected void convert(final Term term) {
			if (term instanceof ApplicationTerm) {
				final ApplicationTerm aterm = (ApplicationTerm) term;
				final String funName = aterm.getFunction().getName();
				if (funName.equals("store")) {
					// its a store
					mStoreTerms.add(aterm);
				} else if (funName.equals("select")) {
					mSelectTerms.add(aterm);
				}
			}
			super.convert(term);
		}
	}

}
