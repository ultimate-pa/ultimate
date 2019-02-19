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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.LocalBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Provides static methods for {@link IProgramVar}s.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class ProgramVarUtils {

	private static final String AUX_VAR_PREFIX = "c_aux_";

	private ProgramVarUtils() {
		// do not instantiate
	}

	public static String generateConstantIdentifierForAuxVar(final TermVariable auxVar) {
		return AUX_VAR_PREFIX + auxVar.getName();
	}

	/**
	 * Construct primed constant for a {@link IProgramVar}
	 *
	 * @param script
	 *            {@link ManagedScript} for which constant is constructed.
	 * @param lockOwner
	 *            Object that currently locks the {@link ManagedScript}.
	 */
	public static ApplicationTerm constructPrimedConstant(final ManagedScript script, final Object lockOwner,
			final Sort sort, final String name) {
		ApplicationTerm primedConstant;
		{
			final String primedConstantName = "c_" + name + "_primed";
			script.declareFun(lockOwner, primedConstantName, new Sort[0], sort);
			primedConstant = (ApplicationTerm) script.term(lockOwner, primedConstantName);
		}
		return primedConstant;
	}

	/**
	 * Construct default constant for a {@link IProgramVar} (The default constant is used in {@link IPredicate}s and as
	 * unprimed instance of variables in {@link TransFormula}s
	 *
	 * @param script
	 *            {@link ManagedScript} for which constant is constructed.
	 * @param lockOwner
	 *            Object that currently locks the {@link ManagedScript}.
	 */
	public static ApplicationTerm constructDefaultConstant(final ManagedScript script, final Object lockOwner,
			final Sort sort, final String name) {
		ApplicationTerm defaultConstant;
		{
			final String defaultConstantName = "c_" + name;
			script.declareFun(lockOwner, defaultConstantName, new Sort[0], sort);
			defaultConstant = (ApplicationTerm) script.term(lockOwner, defaultConstantName);
		}
		return defaultConstant;
	}

	/**
	 * Construct constant for an aux var. (The default constant is used to represent the aux var in the closed formulas
	 * of {@link TransFormula}s.
	 *
	 * @param mgdScript
	 *            {@link ManagedScript} for which constant is constructed.
	 */
	public static ApplicationTerm constructConstantForAuxVar(final ManagedScript mgdScript, final TermVariable auxVar) {
		ApplicationTerm defaultConstant;
		{

			final String defaultConstantName = generateConstantIdentifierForAuxVar(auxVar);
			final Object lockOwner = auxVar;
			mgdScript.lock(lockOwner);
			mgdScript.declareFun(lockOwner, defaultConstantName, new Sort[0], auxVar.getSort());
			defaultConstant = (ApplicationTerm) mgdScript.term(lockOwner, defaultConstantName);
			mgdScript.unlock(lockOwner);
		}
		return defaultConstant;
	}

	/**
	 * Get the constant that represents an auxVar. Requires that this constant has already been declared.
	 */
	public static ApplicationTerm getAuxVarConstant(final ManagedScript mgdScript, final TermVariable auxVar) {
		final String defaultConstantName = generateConstantIdentifierForAuxVar(auxVar);
		return (ApplicationTerm) mgdScript.getScript().term(defaultConstantName);
	}

	public static Set<IProgramNonOldVar> extractNonOldVars(final Term term, final IIcfgSymbolTable symbolTable) {
		final Set<IProgramNonOldVar> result = new HashSet<>();
		for (final TermVariable tv : term.getFreeVars()) {
			final IProgramVar pv = symbolTable.getProgramVar(tv);
			if (pv instanceof IProgramNonOldVar) {
				result.add((IProgramNonOldVar) pv);
			}
		}
		return result;
	}

	public static Set<IProgramOldVar> extractOldVars(final Term term, final IIcfgSymbolTable symbolTable) {
		final Set<IProgramOldVar> result = new HashSet<>();
		for (final TermVariable tv : term.getFreeVars()) {
			final IProgramVar pv = symbolTable.getProgramVar(tv);
			if (pv instanceof IProgramOldVar) {
				result.add((IProgramOldVar) pv);
			}
		}
		return result;
	}

	public static Term renameNonOldGlobalsToOldGlobals(final Term term, final IIcfgSymbolTable symbolTable,
			final ManagedScript mgdScript) {
		final Set<IProgramNonOldVar> nonOldVars = extractNonOldVars(term, symbolTable);
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (final IProgramNonOldVar pv : nonOldVars) {
			if (pv instanceof IProgramNonOldVar) {
				final IProgramOldVar oldVar = pv.getOldVar();
				substitutionMapping.put(pv.getTermVariable(), oldVar.getTermVariable());
			}
		}
		final Term result = (new Substitution(mgdScript, substitutionMapping)).transform(term);
		return result;
	}

	public static Term renameOldGlobalsToNonOldGlobals(final Term term, final IIcfgSymbolTable symbolTable,
			final ManagedScript mgdScript) {
		final Set<IProgramOldVar> oldVars = extractOldVars(term, symbolTable);
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (final IProgramOldVar pv : oldVars) {
			if (pv instanceof IProgramOldVar) {
				final IProgramNonOldVar nonoldVar = pv.getNonOldVar();
				substitutionMapping.put(pv.getTermVariable(), nonoldVar.getTermVariable());
			}
		}
		final Term result = (new Substitution(mgdScript, substitutionMapping)).transform(term);
		return result;
	}

	public static String buildBoogieVarName(final String identifier, final String procedure, final boolean isGlobal,
			final boolean isOldvar) {
		String name;
		if (isGlobal) {
			assert procedure == null;
			if (isOldvar) {
				name = "old(" + identifier + ")";
			} else {
				name = identifier;
			}
		} else {
			assert (!isOldvar) : "only global vars can be oldvars";
			name = procedure + "_" + identifier;
		}
		return name;
	}

	/**
	 * Construct global {@link BoogieNonOldVar} together with corresponding {@link BoogieOldVar} and return the
	 * {@link BoogieNonOldVar}
	 */
	public static BoogieNonOldVar constructGlobalProgramVarPair(final String identifier, final Sort sort,
			final ManagedScript mgdScript, final Object lockOwner) {
		final String procedure = null;
		BoogieOldVar oldVar;
		{
			final boolean isOldVar = true;
			final String name = ProgramVarUtils.buildBoogieVarName(identifier, procedure, true, isOldVar);
			final TermVariable termVariable = mgdScript.variable(name, sort);
			final ApplicationTerm defaultConstant =
					ProgramVarUtils.constructDefaultConstant(mgdScript, lockOwner, sort, name);
			final ApplicationTerm primedConstant =
					ProgramVarUtils.constructPrimedConstant(mgdScript, lockOwner, sort, name);

			oldVar = new BoogieOldVar(identifier, null, termVariable, defaultConstant, primedConstant);
		}
		BoogieNonOldVar nonOldVar;
		{
			final boolean isOldVar = false;
			final String name = ProgramVarUtils.buildBoogieVarName(identifier, procedure, true, isOldVar);
			final TermVariable termVariable = mgdScript.variable(name, sort);
			final ApplicationTerm defaultConstant =
					ProgramVarUtils.constructDefaultConstant(mgdScript, lockOwner, sort, name);
			final ApplicationTerm primedConstant =
					ProgramVarUtils.constructPrimedConstant(mgdScript, lockOwner, sort, name);

			nonOldVar = new BoogieNonOldVar(identifier, null, termVariable, defaultConstant, primedConstant, oldVar);
		}
		oldVar.setNonOldVar(nonOldVar);
		return nonOldVar;
	}

	/**
	 * Construct a new {@link ILocalProgramVar}. The caller has to ensure that the identifier is unique and that the
	 * variable is inserted into a symbol table (if needed).
	 */
	public static ILocalProgramVar constructLocalProgramVar(final String identifier, final String procedure,
			final Sort sort, final ManagedScript mgdScript, final Object lockOwner) {
		final String name = ProgramVarUtils.buildBoogieVarName(identifier, procedure, false, false);
		final TermVariable termVariable = mgdScript.variable(name, sort);
		final ApplicationTerm defaultConstant =
				ProgramVarUtils.constructDefaultConstant(mgdScript, lockOwner, sort, name);
		final ApplicationTerm primedConstant =
				ProgramVarUtils.constructPrimedConstant(mgdScript, lockOwner, sort, name);
		return new LocalBoogieVar(identifier, procedure, null, termVariable, defaultConstant, primedConstant);
	}

}
