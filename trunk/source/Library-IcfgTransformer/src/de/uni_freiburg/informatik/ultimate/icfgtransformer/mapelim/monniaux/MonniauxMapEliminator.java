/*
 * Copyright (C) 2019 Luca Bruder (luca.bruder@gmx.de)
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
package de.uni_freiburg.informatik.ultimate.icfgtransformer.mapelim.monniaux;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.TransformedIcfgBuilder;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.IdentityTransformer;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.BasicIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
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
	private final int mCells;

	public MonniauxMapEliminator(final ILogger logger, final IIcfg<IcfgLocation> icfg,
			final IBacktranslationTracker backtranslationTracker, final int cells) {
		mIcfg = Objects.requireNonNull(icfg);
		mMgdScript = mIcfg.getCfgSmtToolkit().getManagedScript();
		mLogger = logger;
		mBacktranslationTracker = backtranslationTracker;
		mResultIcfg = eliminateMaps();
		mCells = cells;
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

		// Create mappings from original ProgramVars to a set of mCells new ProgramVars
		final Map<IProgramVar, Set<IProgramVar>> idxD = null;
		final Map<IProgramVar, Set<IProgramVar>> valD = null;
		final IIcfgSymbolTable symboltable = mIcfg.getCfgSmtToolkit().getSymbolTable();
		final Set<IProgramNonOldVar> globals = symboltable.getGlobals();
		// mIcfg.getProcedureEntryNodes().keySet(); // set of procedures of this icfg
		// symboltable.getLocals(procedurename) //for each procedure, get the local variables

		// Fill the sets idxD and valD with a certain number (mCells) of new program variables for each old program
		// variable of the sort array
		for (final IProgramVar var : globals) {
			if (var.getSort().isArraySort()) {
				final Set<IProgramVar> idx = null;
				final Set<IProgramVar> val = null;
				for (int i = 0; i < mCells; i++) {
					final String name1 = (var.toString() + "_idx_" + Integer.toString(i));
					final String name2 = (var.toString() + "_val_" + Integer.toString(i));
					/*
					 * final IProgramVar newVar1 = ProgramVarUtils.constructLocalProgramVar(name1, procedure,
					 * var.getSort(), mMgdScript, lockOwner); final IProgramVar newVar2 =
					 * ProgramVarUtils.constructLocalProgramVar(name2, procedure, var.getSort(), mMgdScript, lockOwner);
					 * idx.add(newVar1); val.add(newVar2);
					 */
				}
				idxD.put(var, idx);
				valD.put(var, val);
			}
		}

		while (iter.hasNext()) {
			final IIcfgTransition<?> transition = iter.next();

			final Map<Term, Integer> lowD = null;
			final Map<Term, Integer> highD = null;

			// Iterate over relevant edges
			if (transition instanceof IIcfgInternalTransition) {

				final IIcfgInternalTransition<?> internalTransition = (IIcfgInternalTransition<?>) transition;
				final UnmodifiableTransFormula tf = internalTransition.getTransformula();
				final UnmodifiableTransFormula newtf = tf;
				final Term tfTerm = tf.getFormula();
				final StoreSelectEqualityCollector ssec = new StoreSelectEqualityCollector();
				ssec.transform(tfTerm);
				final Map<Term, Term> subst = new HashMap<>();

				for (final Term selectTerm : ssec.mSelectTerms) {
					final ApplicationTerm aSelectTerm = (ApplicationTerm) selectTerm;
					EliminateSelects(tf, newtf, idxD, valD, aSelectTerm, lowD, highD);
				}
				for (final Term storeTerm : ssec.mStoreTerms) {
					final ApplicationTerm aStoreTerm = (ApplicationTerm) storeTerm;
					EliminateStores(tf, newtf, idxD, valD, aStoreTerm, lowD, highD);
				}
				for (final Term equalityTerm : ssec.mEqualityTerms) {
					final ApplicationTerm aEqualityTerm = (ApplicationTerm) equalityTerm;
					EliminateEqualities(tf, newtf, idxD, valD, aEqualityTerm, lowD, highD);
				}
			} else {
				throw new UnsupportedOperationException("not yet implemented");
			}
		}
	}

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

	private void EliminateSelects(final UnmodifiableTransFormula tf, final UnmodifiableTransFormula new_tf,
			final Map<IProgramVar, Set<IProgramVar>> idxD, final Map<IProgramVar, Set<IProgramVar>> valD,
			final ApplicationTerm selectTerm, final Map<Term, Integer> lowD, final Map<Term, Integer> highD) {
		final Term[] params = selectTerm.getParameters();
		final Term x = params[0];
		final int j = Integer.parseInt(x.toString().replaceAll("\\D", ""));
		if (lowD.get(x) > j) {
			lowD.put(x, j);
		}
		if (highD.get(x) < j) {
			highD.put(x, j);
		}
		// TBD: Actually eliminate the array
	}

	private void EliminateStores(final UnmodifiableTransFormula tf, final UnmodifiableTransFormula new_tf,
			final Map<IProgramVar, Set<IProgramVar>> idxD, final Map<IProgramVar, Set<IProgramVar>> valD,
			final ApplicationTerm storeTerm, final Map<Term, Integer> lowD, final Map<Term, Integer> highD) {
		final Term[] params = storeTerm.getParameters();
		final Term x = params[0];
		final int j = Integer.parseInt(x.toString().replaceAll("\\D", ""));
		if (lowD.get(x) > j) {
			lowD.put(x, j);
		}
		if (highD.get(x) < j) {
			highD.put(x, j);
		}
		// TBD: Actually eliminate the array
	}

	private void EliminateEqualities(final UnmodifiableTransFormula tf, final UnmodifiableTransFormula new_tf,
			final Map<IProgramVar, Set<IProgramVar>> idxD, final Map<IProgramVar, Set<IProgramVar>> valD,
			final ApplicationTerm equalityTerm, final Map<Term, Integer> lowD, final Map<Term, Integer> highD) {
		final Term[] paramsX = equalityTerm.getParameters();
		final Term x = paramsX[0];
		final int j = Integer.parseInt(x.toString().replaceAll("\\D", ""));
		final Term[] paramsY = equalityTerm.getParameters();
		final Term y = paramsY[1];
		final int k = Integer.parseInt(y.toString().replaceAll("\\D", ""));
		if (lowD.get(x) > j) {
			lowD.put(x, j);
		}
		if (highD.get(x) < j) {
			highD.put(x, j);
		}
		if (lowD.get(y) > k) {
			lowD.put(y, k);
		}
		if (highD.get(y) < k) {
			highD.put(y, k);
		}
		// TBD: Actually eliminate the array
	}

}
