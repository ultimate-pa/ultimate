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

import java.math.BigInteger;
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
		
		
		final HashMap<TermVariable, Integer> varMatrixIndex = determineMatrixIndices(su);
		final int n = varMatrixIndex.size() + 1;
		
		// Initialize update matrix with identity matrix (every variable assigned to itself).
		final QuadraticMatrix updateMatrix = QuadraticMatrix.identityMatrix(n);
		
		for (final Entry<IProgramVar, Term> update : su.getUpdatedVars().entrySet()) {
			final IPolynomialTerm polyRhs =
			(IPolynomialTerm) new PolynomialTermTransformer(mMgdScript.getScript()).transform(update.getValue());
			
			fillMatrixRow(updateMatrix, varMatrixIndex, polyRhs, update.getKey());
		}
		
		final QuadraticMatrix jordanUpdate = updateMatrix.jordanMatrix();
		final RationalMatrix modalUpdate = QuadraticMatrix.modalMatrix(updateMatrix, jordanUpdate);
		final RationalMatrix inverseModalUpdate = RationalMatrix.inverse(modalUpdate);
	}
	
	/**Go through terms, get all variables and create a hash map varMatrixIndex with variables as key and corresponding
	 * matrix index as value to save which column corresponds to which variable
	 * and which row corresponds to which update.
	 * @param su SimultaneousUpdate to process
	 * @return HashMap varMatrixIndex mapping variables to indices
	 */
	private static HashMap<TermVariable, Integer> determineMatrixIndices(final SimultaneousUpdate su) {
		HashMap<TermVariable, Integer> varMatrixIndex = new HashMap<TermVariable, Integer>();
		int i = -1;
		for (IProgramVar updatedVar : su.getUpdatedVars().keySet()) {
			if (!varMatrixIndex.containsKey(updatedVar.getTermVariable())) {
				i = i + 1;
				// add all updated variables.
				varMatrixIndex.put(updatedVar.getTermVariable(), i);
			}	
			// add all not updated variables.
			TermVariable[] variables = su.getUpdatedVars().get(updatedVar).getFreeVars();
			for (TermVariable var : variables) {
				if (!varMatrixIndex.containsKey(var)) {
					i = i + 1;
					varMatrixIndex.put(var, i);
				}
			}
		}
		return varMatrixIndex;
	}
	
	/**
	 * Fills the row corresponding to variable of the updateMatrix where variable is updated with polyRhs.
	 * @param updateMatrix matrix to fill
	 * @param varMatrixIndex HashMap containing variables and corresponding matrix indices
	 * @param polyRhs processed update polynomial
	 * @param variable that is updated with polynomial
	 */
	private static void fillMatrixRow(QuadraticMatrix updateMatrix, final HashMap<TermVariable, Integer> varMatrixIndex,
			final IPolynomialTerm polyRhs, final IProgramVar variable) {
		
		final int n = updateMatrix.mDimension - 1;
		updateMatrix.mEntries[n][n] = BigInteger.valueOf(1);
		// Set diagonal entry to 0 for case variable assignment does not depend on variable itself
		// (matrix was initialized as identity matrix).
		updateMatrix.mEntries[varMatrixIndex.get(variable.getTermVariable())]
				[varMatrixIndex.get(variable.getTermVariable())] = BigInteger.valueOf(0);
		
		// Fill row.
		for (TermVariable termVar : varMatrixIndex.keySet()) {
			updateMatrix.mEntries[varMatrixIndex.get(variable.getTermVariable())][varMatrixIndex.get(termVar)] =
					determineCoefficient(polyRhs, termVar);
			updateMatrix.mEntries[varMatrixIndex.get(variable.getTermVariable())][n] = determineConstant(polyRhs);
		}
	}
	
	/**
	 * @param polyRhs
	 * @param termVar
	 * @return coefficient of termVar in the polynomial polyRhs.
	 */
	private static BigInteger determineCoefficient(final IPolynomialTerm polyRhs, final TermVariable termVar) {
		for (Monomial monom : polyRhs.getMonomial2Coefficient().keySet()) {
			if (!(monom.isLinear())) {
				throw new AssertionError("Some term is not linear.");
			}
			if (monom.getSingleVariable().equals(termVar)) {
				Rational coefficient = polyRhs.getMonomial2Coefficient().get(monom);
				if (!(coefficient.denominator().equals(BigInteger.valueOf(1)))) {
					throw new AssertionError("Some coefficient is not integral.");
				}
				return coefficient.numerator();
			}
		}
		return BigInteger.valueOf(0);
	}
	
	/**
	 * @param polyRhs
	 * @return constant term of polynomial polyRhs.
	 */
	private static BigInteger determineConstant(final IPolynomialTerm polyRhs) {
		final Rational constant = polyRhs.getConstant();
		if (!(constant.denominator().equals(BigInteger.valueOf(1)))) {
			throw new AssertionError("Constant in some term is not integral.");
		}
		return constant.numerator();
	}

	@Override
	public IIcfg<OUTLOC> getResult() {
		return null;
	}
}