/*
 * Copyright (C) 2020 Jonas Werner (wernerj@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE accelerated interpolation library .
 *
 * The ULTIMATE framework is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE framework is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE accelerated interpolation library . If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PDR library , or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE accelerated interpolation library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.looppreprocessor;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.DNF;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.ModuloNeighborTransformation;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.RemoveNegation;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.RewriteDisequality;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.RewriteDivision;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.RewriteIte;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.TermException;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class LoopPreprocessorTransformulaTransformer {

	/**
	 * In case of modulo transformation we get a disjunction covering different cases of integer value intervals. For
	 * acceleration split these disjunctions for underapprox
	 *
	 * @param loopRelation
	 * @return
	 */
	public static List<UnmodifiableTransFormula> splitDisjunction(final ModifiableTransFormula loopRelation,
			final ManagedScript managedScript, final IUltimateServiceProvider services) {
		final DNF dnfConverter = new DNF(services);
		ModifiableTransFormula dnfModTf;
		try {
			dnfModTf = dnfConverter.process(managedScript, loopRelation);
		} catch (final TermException e) {
			e.printStackTrace();
			throw new UnsupportedOperationException("Could not turn into DNF");
		}
		final List<UnmodifiableTransFormula> result = new ArrayList<>();
		final ApplicationTerm dnfAppTerm = (ApplicationTerm) dnfModTf.getFormula();
		if (dnfAppTerm.getFunction().getName() != "or") {
			result.add(buildFormula(loopRelation, loopRelation.getFormula(), managedScript));
		} else {
			for (final Term disjunct : dnfAppTerm.getParameters()) {
				final TransFormulaBuilder tfb = new TransFormulaBuilder(loopRelation.getInVars(),
						loopRelation.getOutVars(), true, null, true, null, false);
				tfb.setFormula(disjunct);
				tfb.addAuxVarsButRenameToFreshCopies(loopRelation.getAuxVars(), managedScript);
				tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
				result.add(tfb.finishConstruction(managedScript));
			}
		}
		return result;
	}

	/**
	 * Rewrite not formulas such as != and not(< x y)
	 *
	 * @param loopRelation
	 * @return
	 */
	public static UnmodifiableTransFormula notTransformation(final ModifiableTransFormula loopRelation,
			final ManagedScript managedScript) {
		final RemoveNegation rn = new RemoveNegation();
		final RewriteDisequality rd = new RewriteDisequality();
		ModifiableTransFormula negFreeTf;
		try {
			negFreeTf = rn.process(managedScript, loopRelation);
			negFreeTf = rd.process(managedScript, negFreeTf);
		} catch (final TermException e) {
			negFreeTf = null;
			e.printStackTrace();
		}
		assert negFreeTf != null;
		return buildFormula(loopRelation, negFreeTf.getFormula(), managedScript);
	}

	/**
	 * substitute modulo by a disjunction
	 *
	 * @param loopRelation
	 * @return
	 */
	public static UnmodifiableTransFormula moduloTransformation(final ModifiableTransFormula loopRelation,
			final ManagedScript managedScript, final ReplacementVarFactory replacementVarFactory,
			final IUltimateServiceProvider services) {
		final ModuloNeighborTransformation modNeighborTransformer = new ModuloNeighborTransformation(services, true);
		ModifiableTransFormula modTfTransformed;
		try {
			modTfTransformed = modNeighborTransformer.process(managedScript, loopRelation);
		} catch (final TermException e) {
			modTfTransformed = null;
			e.printStackTrace();
		}

		final List<Term> result = new ArrayList<>();
		final ApplicationTermFinder applicationTermFinder = new ApplicationTermFinder("mod", false);
		if (modTfTransformed != null) {
			final ApplicationTerm modAppTermTransformed = (ApplicationTerm) modTfTransformed.getFormula();
			for (final Term param : modAppTermTransformed.getParameters()) {
				if (applicationTermFinder.findMatchingSubterms(param).isEmpty()) {
					result.add(param);
				}
			}
		}
		final Term disjunctionNoMod = SmtUtils.or(managedScript.getScript(), result);
		return buildFormula(loopRelation, disjunctionNoMod, managedScript);
	}

	public static UnmodifiableTransFormula iteTransformation(final ModifiableTransFormula loopRelation,
			final ManagedScript managedScript) {
		final RewriteIte rite = new RewriteIte();
		ModifiableTransFormula iteModTf;
		try {
			iteModTf = rite.process(managedScript, loopRelation);
		} catch (final TermException e) {
			iteModTf = null;
			e.printStackTrace();
		}
		assert iteModTf != null;
		return buildFormula(loopRelation, iteModTf.getFormula(), managedScript);
	}

	/**
	 * Rewrite division
	 *
	 * @param loopRelation
	 * @return
	 */
	public static UnmodifiableTransFormula divisionTransformation(final ModifiableTransFormula loopRelation,
			final ManagedScript managedScript, final ReplacementVarFactory replacementVarFactory) {
		final RewriteDivision rd = new RewriteDivision(replacementVarFactory);
		ModifiableTransFormula divModTf;
		try {
			divModTf = rd.process(managedScript, loopRelation);
		} catch (final TermException e) {
			divModTf = null;
			e.printStackTrace();
		}
		assert divModTf != null;
		return buildFormula(loopRelation, divModTf.getFormula(), managedScript);
	}

	public static UnmodifiableTransFormula buildFormula(final ModifiableTransFormula origin, final Term term,
			final ManagedScript managedScript) {
		final TransFormulaBuilder tfb =
				new TransFormulaBuilder(origin.getInVars(), origin.getOutVars(), true, null, true, null, false);
		tfb.setFormula(term);
		tfb.addAuxVarsButRenameToFreshCopies(origin.getAuxVars(), managedScript);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		return tfb.finishConstruction(managedScript);
	}
}
