/*
 * Copyright (C) 2016 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.mapelimination;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.IReplacementVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.IReplacementVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public final class MapEliminatorUtils {
	private MapEliminatorUtils() {
		// Prevent instantiation of this utility class
	}

	private static Term getLocalTerm(final Term term, final ModifiableTransFormula transformula,
			final ManagedScript managedScript, final IIcfgSymbolTable symbolTable, final boolean returnInVar) {
		final Map<Term, Term> substitution = new HashMap<>();
		for (final TermVariable var : term.getFreeVars()) {
			final IProgramVar programVar = symbolTable.getProgramVar(var);
			// Add the missing in-/out-vars to the transformula if necessary
			final TermVariable freshTermVar = getFreshTermVar(var, managedScript);
			if (!transformula.getInVars().containsKey(programVar)) {
				transformula.addInVar(programVar, freshTermVar);
			}
			if (!transformula.getOutVars().containsKey(programVar)) {
				transformula.addOutVar(programVar, freshTermVar);
			}
			// Put the in-/out-var-version of this variable to the substitution-map
			if (returnInVar) {
				substitution.put(var, transformula.getInVars().get(programVar));
			} else {
				substitution.put(var, transformula.getOutVars().get(programVar));
			}
		}
		return new Substitution(managedScript, substitution).transform(term);
	}

	/**
	 * Given a definition as {@code term}, adds the needed in- and out-vars to the transformula and returns the term
	 * with in-vars.
	 *
	 * @param term
	 *            A SMT-Term with global variables
	 * @param transformula
	 *            A TransFormula
	 * @param managedScript
	 *            ManagedScript
	 * @param symbolTable
	 *            SymbolTable
	 * @return The local in-var-term for the given global term
	 */
	public static Term getInVarTerm(final Term term, final ModifiableTransFormula transformula,
			final ManagedScript managedScript, final IIcfgSymbolTable symbolTable) {
		return getLocalTerm(term, transformula, managedScript, symbolTable, true);
	}

	/**
	 * Given a definition as {@code term}, adds the needed in- and out-vars to the transformula and returns the term
	 * with out-vars.
	 *
	 * @param term
	 *            A SMT-Term with global variables
	 * @param transformula
	 *            A TransFormula
	 * @param managedScript
	 *            ManagedScript
	 * @param symbolTable
	 *            SymbolTable
	 * @return The local out-var-term for the given global term
	 */
	public static Term getOutVarTerm(final Term term, final ModifiableTransFormula transformula,
			final ManagedScript managedScript, final IIcfgSymbolTable symbolTable) {
		return getLocalTerm(term, transformula, managedScript, symbolTable, false);
	}

	/**
	 * Given an ArrayIndex of definitions, adds the needed in- and out-vars to the transformula and returns the index
	 * with in-vars.
	 *
	 * @param term
	 *            An array-index with global variables
	 * @param transformula
	 *            A TransFormula
	 * @param managedScript
	 *            ManagedScript
	 * @param symbolTable
	 *            SymbolTable
	 * @return The local in-var-index for the given global index
	 */
	public static ArrayIndex getInVarIndex(final ArrayIndex index, final ModifiableTransFormula transformula,
			final ManagedScript managedScript, final IIcfgSymbolTable symbolTable) {
		final List<Term> list = new ArrayList<>();
		for (final Term t : index) {
			list.add(getInVarTerm(t, transformula, managedScript, symbolTable));
		}
		return new ArrayIndex(list);
	}

	/**
	 * Given an ArrayIndex of definitions, adds the needed in- and out-vars to the transformula and returns the index
	 * with out-vars.
	 *
	 * @param term
	 *            An array-index with global variables
	 * @param transformula
	 *            A TransFormula
	 * @param managedScript
	 *            ManagedScript
	 * @param symbolTable
	 *            SymbolTable
	 * @return The local out-var-index for the given global index
	 */
	public static ArrayIndex getOutVarIndex(final ArrayIndex index, final ModifiableTransFormula transformula,
			final ManagedScript managedScript, final IIcfgSymbolTable symbolTable) {
		final List<Term> list = new ArrayList<>();
		for (final Term t : index) {
			list.add(getOutVarTerm(t, transformula, managedScript, symbolTable));
		}
		return new ArrayIndex(list);
	}

	private static TermVariable getFreshTermVar(final Term term, final ManagedScript managedScript) {
		return managedScript.constructFreshTermVariable(niceTermString(term), term.getSort());
	}

	private static String niceTermString(final Term term) {
		if (SmtUtils.isFunctionApplication(term, "select")) {
			final StringBuilder stringBuilder = new StringBuilder();
			final MultiDimensionalSelect select = new MultiDimensionalSelect(term);
			stringBuilder.append("array_").append(niceTermString(select.getArray())).append('[');
			final ArrayIndex index = select.getIndex();
			for (int i = 0; i < index.size(); i++) {
				stringBuilder.append(niceTermString(index.get(i))).append(i == index.size() - 1 ? ']' : ',');
			}
			return stringBuilder.toString();
		}
		if (term instanceof ApplicationTerm && !SmtUtils.isConstant(term)) {
			final StringBuilder stringBuilder = new StringBuilder();
			final ApplicationTerm applicationTerm = (ApplicationTerm) term;
			final FunctionSymbol function = applicationTerm.getFunction();
			if (!function.isIntern()) {
				stringBuilder.append("uf_");
			}
			stringBuilder.append('(').append(function.getName()).append(' ');
			final Term[] params = applicationTerm.getParameters();
			for (int i = 0; i < params.length; i++) {
				stringBuilder.append(niceTermString(params[i])).append(i == params.length - 1 ? ')' : ' ');
			}
			return stringBuilder.toString();
		}
		return SmtUtils.removeSmtQuoteCharacters(term.toString());
	}

	/**
	 * Adds a replacementVar constructed by {@code replacementVarFactory} with the given {@code term} as definition to
	 * the in- and out-vars of the given {@code transformula}.
	 */
	public static void addReplacementVar(final Term term, final ModifiableTransFormula transformula,
			final ManagedScript managedScript, final ReplacementVarFactory replacementVarFactory,
			final IIcfgSymbolTable symbolTable) {
		final IReplacementVarOrConst varOrConst = replacementVarFactory.getOrConstuctReplacementVar(term, false);
		if (varOrConst instanceof ReplacementConst) {
			throw new UnsupportedOperationException("not yet implemented");
		} else if (varOrConst instanceof IReplacementVar) {
			final IReplacementVar var = (IReplacementVar) varOrConst;
			boolean containsAssignedVar = false;
			for (final TermVariable tv : term.getFreeVars()) {
				final IProgramVar progVar = symbolTable.getProgramVar(tv);
				if (transformula.getInVars().get(progVar) != transformula.getOutVars().get(progVar)) {
					containsAssignedVar = true;
					break;
				}
			}
			final TermVariable termVar = getFreshTermVar(term, managedScript);
			if (!transformula.getInVars().containsKey(var)) {
				transformula.addInVar(var, termVar);
			}
			if (!transformula.getOutVars().containsKey(var)) {
				// If the term contains an assigned var, different in- and out-vars are created, otherwise the
				// same
				if (containsAssignedVar) {
					transformula.addOutVar(var, getFreshTermVar(term, managedScript));
				} else {
					transformula.addOutVar(var, termVar);
				}
			}
		} else {
			throw new AssertionError("illegal type " + varOrConst.getClass());
		}
	}

	/**
	 * Returns the corresponding replacementVar (or auxVar) for the given {@code term} constructed by
	 * {@code replacementVarFactory}. The replacementVars have to be already to it added by calling
	 * {@code addReplacementVar} for each term given to this method. If an aux-var is created, it is added to
	 * {@code auxVars}.
	 */
	public static Term getReplacementVar(final Term term, final ModifiableTransFormula transformula,
			final Script script, final ReplacementVarFactory replacementVarFactory,
			final Collection<TermVariable> auxVars) {
		if (!ModifiableTransFormulaUtils.allVariablesAreInVars(term, transformula)
				&& !ModifiableTransFormulaUtils.allVariablesAreOutVars(term, transformula)) {
			return getAndAddAuxVar(term, auxVars, replacementVarFactory);
		}
		final Term definition =
				ModifiableTransFormulaUtils.translateTermVariablesToDefinitions(script, transformula, term);
		final IReplacementVarOrConst varOrConst = replacementVarFactory.getOrConstuctReplacementVar(definition, false);
		if (varOrConst instanceof ReplacementConst) {
			throw new UnsupportedOperationException("not yet implemented");
		} else if (varOrConst instanceof IReplacementVar) {
			final IReplacementVar var = (IReplacementVar) varOrConst;
			assert transformula.getInVars().containsKey(var) && transformula.getOutVars().containsKey(var) : var
					+ " was not added to the transformula!";
			if (ModifiableTransFormulaUtils.allVariablesAreInVars(term, transformula)) {
				return transformula.getInVars().get(var);
			}
			return transformula.getOutVars().get(var);
		} else {
			throw new AssertionError("illegal type " + varOrConst.getClass());
		}
	}

	/**
	 * Returns an aux-var constructed by {@code replacementVarFactory}for the given {@code term} and adds it to
	 * {@code auxVars}. The method returns the same aux-var for two terms iff they're equal.
	 */
	public static TermVariable getAndAddAuxVar(final Term term, final Collection<TermVariable> auxVars,
			final ReplacementVarFactory replacementVarFactory) {
		final TermVariable auxVar = replacementVarFactory.getOrConstructAuxVar(niceTermString(term), term.getSort());
		auxVars.add(auxVar);
		return auxVar;
	}
}
