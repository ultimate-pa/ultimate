/*
 * Copyright (C) 2021 Miriam Herzig
 * Copyright (C) 2021 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan;

import java.util.HashMap;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IBacktranslationTracker;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.IIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ILocationFactory;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.biesenbach.LoopExtraction;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.biesenbach.SimpleLoop;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.SimultaneousUpdate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.IPolynomialTerm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.Monomial;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialTermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * @author Miriam Herzig
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class JordanLoopAcceleration<INLOC extends IcfgLocation, OUTLOC extends IcfgLocation>
		implements IIcfgTransformer<OUTLOC> {

	final ILogger mLogger;
	final IIcfg<INLOC> mOriginalIcfg;
	final Class<OUTLOC> mOutLocationClass;
	final ILocationFactory<INLOC, OUTLOC> mFunLocFac;
	final String mNewIcfgIdentifier;
	final ITransformulaTransformer mTransformer;
	final IBacktranslationTracker mBacktranslationTracker;
	final IUltimateServiceProvider mServices;

	public JordanLoopAcceleration(final ILogger logger, final IIcfg<INLOC> originalIcfg,
			final Class<OUTLOC> outLocationClass, final ILocationFactory<INLOC, OUTLOC> funLocFac,
			final String newIcfgIdentifier, final ITransformulaTransformer transformer,
			final IBacktranslationTracker backtranslationTracker, final IUltimateServiceProvider services) {

		//Setup
		mLogger = logger;
		mOriginalIcfg = originalIcfg;
		mOutLocationClass = outLocationClass;
		mFunLocFac = funLocFac;
		mNewIcfgIdentifier = newIcfgIdentifier;
		mTransformer = transformer;
		mBacktranslationTracker = backtranslationTracker;
		mServices = services;

		accelerateAll();
	}

	private IIcfg<OUTLOC> accelerateAll() {
		final LoopExtraction<INLOC, OUTLOC> loopExtraction = new LoopExtraction<>(mLogger, mOriginalIcfg);
		for(final SimpleLoop loop : loopExtraction.getLoopTransFormulas()){
			accelerateLoop(loop.mLoopTransFormula);
		}
		return null;
	}

	private void accelerateLoop(final UnmodifiableTransFormula loopTransFormula) {
		final ManagedScript mMgdScript = mOriginalIcfg.getCfgSmtToolkit().getManagedScript();
		final UnmodifiableTransFormula guardTf =
				TransFormulaUtils.computeGuard(loopTransFormula, mMgdScript, mServices, mLogger);
		mLogger.info("Guard: " + guardTf);
		final SimultaneousUpdate su = new SimultaneousUpdate(loopTransFormula, mMgdScript);
		
		
		final HashMap<TermVariable, Integer> var_matrix_index = determine_matrix_indices(su);
		final int n = var_matrix_index.size() + 1;
		
		// Initialize update matrix with identity matrix.
		// (every variable assigned to itself.)
		final QuadraticMatrix UpdateMatrix = QuadraticMatrix.identity_matrix(n);
		
		for (final Entry<IProgramVar, Term> update : su.getUpdatedVars().entrySet()) {
			final IPolynomialTerm polyRhs =
			(IPolynomialTerm) new PolynomialTermTransformer(mMgdScript.getScript()).transform(update.getValue());
			
			fill_matrix_row(UpdateMatrix, var_matrix_index, polyRhs, update.getKey());
		}
		
		final QuadraticMatrix JordanUpdate = UpdateMatrix.jordan_matrix();
		final RationalMatrix ModalUpdate = QuadraticMatrix.modal_matrix(UpdateMatrix, JordanUpdate);
		final RationalMatrix InverseModalUpdate = RationalMatrix.inverse(ModalUpdate);
	}
	
	private static HashMap<TermVariable, Integer> determine_matrix_indices(final SimultaneousUpdate su) {
		// Go through terms and get all variables and
		// create a hash map var_matrix_index with variables as key and
		// corresponding matrix index as value
		// to save which column corresponds to which variable
		// and which row corresponds to which update.
		HashMap<TermVariable, Integer> var_matrix_index = new HashMap<TermVariable, Integer>();
		int i = -1;
		for (IProgramVar updated_var : su.getUpdatedVars().keySet()) {
			if (!var_matrix_index.containsKey(updated_var.getTermVariable())) {
				i = i + 1;
				// add all updated variables.
				var_matrix_index.put(updated_var.getTermVariable(), i);
			}
					
			// add all not updated variables.
			TermVariable[] variables = su.getUpdatedVars().get(updated_var).getFreeVars();
			for (TermVariable var : variables) {
				if (!var_matrix_index.containsKey(var)) {
					i = i + 1;
					var_matrix_index.put(var, i);
				}
			}
		}
		return var_matrix_index;
	}
	
	private static void fill_matrix_row(QuadraticMatrix UpdateMatrix, final HashMap<TermVariable, Integer> var_matrix_index, final IPolynomialTerm polyRhs, final IProgramVar variable) {
		// Fills the row corresponding to variable of the UpdateMatrix
		// where variable is updated with polyRhs.
		
		final int n = UpdateMatrix.dimension - 1;
		UpdateMatrix.entries[n][n] = 1;
		// Set diagonal entry to 0 for case variable assignment does not depend on variable itself
		// (matrix was initialized as identity matrix).
		UpdateMatrix.entries[var_matrix_index.get(variable.getTermVariable())][var_matrix_index.get(variable.getTermVariable())] = 0;
		
		// Fill row.
		for (TermVariable term_var : var_matrix_index.keySet()) {
			UpdateMatrix.entries[var_matrix_index.get(variable.getTermVariable())][var_matrix_index.get(term_var)] = determine_coefficient(polyRhs, term_var);
			UpdateMatrix.entries[var_matrix_index.get(variable.getTermVariable())][n] = determine_constant(polyRhs);
		}
	}
	
	private static int determine_coefficient(final IPolynomialTerm polyRhs, final TermVariable term_var) {
		// Determines coefficient of term_var in the polynomial polyRhs.
		
		for (Monomial monom : polyRhs.getMonomial2Coefficient().keySet()) {
			if (!(monom.isLinear())) {
				throw new AssertionError("Some term is not linear.");
			}
			if (monom.getSingleVariable().equals(term_var)) {
				Rational coefficient = polyRhs.getMonomial2Coefficient().get(monom);
				// BigInteger?
				if (coefficient.denominator().intValue() != 1) {
					throw new AssertionError("Some coefficient is not integral.");
				}
				// BigInteger?
				return coefficient.numerator().intValue();
			}
		}
		return 0;
	}
	
	private static int determine_constant(final IPolynomialTerm polyRhs) {
		// Determines constant of polynomial polyRhs.
		
		final Rational constant = polyRhs.getConstant();
		// BigInteger?
		if (constant.denominator().intValue() != 1) {
			throw new AssertionError("Constant in some term is not integral.");
		}
		// BigInteger?
		return constant.numerator().intValue();
	}

	@Override
	public IIcfg<OUTLOC> getResult() {
		return null;
	}
}