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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.IReplacementVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

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
			if (pv != null) {
				final IProgramOldVar oldVar = pv.getOldVar();
				substitutionMapping.put(pv.getTermVariable(), oldVar.getTermVariable());
			}
		}
		final Term result = Substitution.apply(mgdScript, substitutionMapping, term);
		return result;
	}

	public static Term renameOldGlobalsToNonOldGlobals(final Term term, final IIcfgSymbolTable symbolTable,
			final ManagedScript mgdScript) {
		final Set<IProgramOldVar> oldVars = extractOldVars(term, symbolTable);
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (final IProgramOldVar pv : oldVars) {
			if (pv != null) {
				final IProgramNonOldVar nonoldVar = pv.getNonOldVar();
				substitutionMapping.put(pv.getTermVariable(), nonoldVar.getTermVariable());
			}
		}
		final Term result = Substitution.apply(mgdScript, substitutionMapping, term);
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
	 * Construct global {@link ProgramNonOldVar} together with corresponding {@link ProgramOldVar} and return the
	 * {@link ProgramNonOldVar}
	 */
	public static ProgramNonOldVar constructGlobalProgramVarPair(final String identifier, final Sort sort,
			final ManagedScript mgdScript, final Object lockOwner) {
		final String procedure = null;
		ProgramOldVar oldVar;
		{
			final boolean isOldVar = true;
			final String name = ProgramVarUtils.buildBoogieVarName(identifier, procedure, true, isOldVar);
			final TermVariable termVariable = mgdScript.variable(name, sort);
			final ApplicationTerm defaultConstant =
					ProgramVarUtils.constructDefaultConstant(mgdScript, lockOwner, sort, name);
			final ApplicationTerm primedConstant =
					ProgramVarUtils.constructPrimedConstant(mgdScript, lockOwner, sort, name);

			oldVar = new ProgramOldVar(identifier, termVariable, defaultConstant, primedConstant);
		}
		ProgramNonOldVar nonOldVar;
		{
			final boolean isOldVar = false;
			final String name = ProgramVarUtils.buildBoogieVarName(identifier, procedure, true, isOldVar);
			final TermVariable termVariable = mgdScript.variable(name, sort);
			final ApplicationTerm defaultConstant =
					ProgramVarUtils.constructDefaultConstant(mgdScript, lockOwner, sort, name);
			final ApplicationTerm primedConstant =
					ProgramVarUtils.constructPrimedConstant(mgdScript, lockOwner, sort, name);

			nonOldVar = new ProgramNonOldVar(identifier, termVariable, defaultConstant, primedConstant, oldVar);
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
		return new LocalProgramVar(identifier, procedure, termVariable, defaultConstant, primedConstant);
	}

	/**
	 * Apply a {@link TermTransferrer} to an {@link IProgramVar} to transfer a programvar representation between
	 * solvers.
	 *
	 * Note that this method does not provide a cache, i.e., if you call it multiple times on the same <code>pv</code>
	 * instance, you get multiple instances back. You need to use your own caching based on your context to avoid this.
	 */
	public static IProgramVar transferProgramVar(final TermTransferrer tt, final IProgramVar pv) {
		if (pv instanceof ILocalProgramVar) {
			return new TransferredLocalProgramVar((ILocalProgramVar) pv, tt);
		} else if (pv instanceof IProgramNonOldVar) {
			return new TransferredProgramNonOldVar((IProgramNonOldVar) pv, tt);
		} else if (pv instanceof IProgramOldVar) {
			return new TransferredProgramNonOldVar(((IProgramOldVar) pv).getNonOldVar(), tt).getOldVar();
		} else if (pv instanceof IReplacementVar) {
			return new TransferredReplacementVar((IReplacementVar) pv, tt);
		} else {
			return new TransferredProgramVar<>(pv, tt);
		}
	}

	/**
	 * Apply a {@link TermTransferrer} to an {@link IProgramConst} to transfer a program constant representation between
	 * solvers.
	 *
	 * Note that this method does not provide a cache, i.e., if you call it multiple times on the same
	 * <code>progConst</code> instance, you get multiple instances back. You need to use your own caching based on your
	 * context to avoid this.
	 */

	public static IProgramConst transferProgramConst(final TermTransferrer tt, final IProgramConst progConst) {
		return new TransferredProgramConst(progConst, tt);
	}

	private static final class TransferredProgramConst implements IProgramConst {
		private final IProgramConst mProgConst;
		private final Term mTerm;
		private final ApplicationTerm mDefaultConst;
		private static final long serialVersionUID = 1L;

		private TransferredProgramConst(final IProgramConst progConst, final TermTransferrer tt) {
			mProgConst = progConst;
			mTerm = tt.transform(progConst.getTerm());
			mDefaultConst = (ApplicationTerm) tt.transform(progConst.getDefaultConstant());
		}

		@Override
		public String getGloballyUniqueId() {
			return mProgConst.getGloballyUniqueId();
		}

		@Override
		public boolean isGlobal() {
			return mProgConst.isGlobal();
		}

		@Override
		public Term getTerm() {
			return mTerm;
		}

		@Override
		public String getIdentifier() {
			return mProgConst.getIdentifier();
		}

		@Override
		public ApplicationTerm getDefaultConstant() {
			return mDefaultConst;
		}

		@Override
		public String toString() {
			return mProgConst.toString();
		}
	}

	/**
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	private static class TransferredProgramVar<L extends IProgramVar> implements IProgramVar {
		private static final long serialVersionUID = 1L;
		protected final L mOriginalProgramVar;
		private final Term mTerm;
		private final TermVariable mTermVar;
		private final ApplicationTerm mPrimedConstant;
		private final ApplicationTerm mDefaultConstant;

		private TransferredProgramVar(final L pv, final TermTransferrer tt) {
			mOriginalProgramVar = pv;
			mTerm = tt.transform(pv.getTerm());
			mTermVar = (TermVariable) tt.transform(pv.getTermVariable());
			mPrimedConstant = (ApplicationTerm) tt.transform(pv.getPrimedConstant());
			mDefaultConstant = (ApplicationTerm) tt.transform(pv.getDefaultConstant());

		}

		@Override
		public String getGloballyUniqueId() {
			return mOriginalProgramVar.getGloballyUniqueId();
		}

		@Override
		public boolean isGlobal() {
			return mOriginalProgramVar.isGlobal();
		}

		@Override
		public Term getTerm() {
			return mTerm;
		}

		@Override
		public boolean isOldvar() {
			return mOriginalProgramVar.isOldvar();
		}

		@Override
		public TermVariable getTermVariable() {
			return mTermVar;
		}

		@Override
		public String getProcedure() {
			return mOriginalProgramVar.getProcedure();
		}

		@Override
		public ApplicationTerm getPrimedConstant() {
			return mPrimedConstant;
		}

		@Override
		public ApplicationTerm getDefaultConstant() {
			return mDefaultConstant;
		}

		@Override
		public String toString() {
			return mOriginalProgramVar.toString();
		}
	}

	private static class TransferredLocalProgramVar extends TransferredProgramVar<ILocalProgramVar>
			implements ILocalProgramVar {

		private static final long serialVersionUID = 1L;

		public TransferredLocalProgramVar(final ILocalProgramVar pv, final TermTransferrer tt) {
			super(pv, tt);
		}

		@Override
		public String getIdentifier() {
			return mOriginalProgramVar.getIdentifier();
		}
	}

	private static class TransferredProgramNonOldVar implements IProgramNonOldVar {

		private static final long serialVersionUID = 1L;
		private final IProgramVar mNonOld;
		private final IProgramOldVar mOld;
		private final String mIdentifier;

		public TransferredProgramNonOldVar(final IProgramNonOldVar nonOldPv, final TermTransferrer tt) {
			mNonOld = new TransferredProgramVar<IProgramVar>(nonOldPv, tt);
			mOld = new TransferredProgramOldVar(this, nonOldPv.getOldVar(), tt);
			mIdentifier = nonOldPv.getIdentifier();
		}

		@Override
		public TermVariable getTermVariable() {
			return mNonOld.getTermVariable();
		}

		@Override
		public ApplicationTerm getDefaultConstant() {
			return mNonOld.getDefaultConstant();
		}

		@Override
		public ApplicationTerm getPrimedConstant() {
			return mNonOld.getPrimedConstant();
		}

		@Override
		public Term getTerm() {
			return mNonOld.getTerm();
		}

		@Override
		public String getIdentifier() {
			return mIdentifier;
		}

		@Override
		public IProgramOldVar getOldVar() {
			return mOld;
		}

		@Override
		public String toString() {
			return mNonOld.toString();
		}
	}

	private static class TransferredProgramOldVar implements IProgramOldVar {

		private static final long serialVersionUID = 1L;
		private final IProgramVar mOld;
		private final IProgramNonOldVar mNonOld;

		/**
		 * Note that you **must** create this class by creating a TransferredProgramNonOldVar, i.e., you should never
		 * call this constructor directly.
		 *
		 * @param newNonOldVar
		 *            An already transferred {@link IProgramNonOldVar}
		 * @param oldOldVar
		 *            a non-transferred {@link IProgramOldVar}
		 * @param tt
		 *            a {@link TermTransferrer} instance
		 */
		private TransferredProgramOldVar(final IProgramNonOldVar newNonOldVar, final IProgramOldVar oldOldVar,
				final TermTransferrer tt) {
			mOld = new TransferredProgramVar<IProgramVar>(oldOldVar, tt);
			mNonOld = newNonOldVar;
		}

		@Override
		public TermVariable getTermVariable() {
			return mOld.getTermVariable();
		}

		@Override
		public ApplicationTerm getDefaultConstant() {
			return mOld.getDefaultConstant();
		}

		@Override
		public ApplicationTerm getPrimedConstant() {
			return mOld.getPrimedConstant();
		}

		@Override
		public Term getTerm() {
			return mOld.getTerm();
		}

		@Override
		public String getIdentifierOfNonOldVar() {
			return mNonOld.getIdentifier();
		}

		@Override
		public IProgramNonOldVar getNonOldVar() {
			return mNonOld;
		}

		@Override
		public String toString() {
			return mOld.toString();
		}
	}

	private static class TransferredReplacementVar extends TransferredProgramVar<IReplacementVar>
			implements IReplacementVar {

		private static final long serialVersionUID = 1L;
		private final Term mDefinition;

		public TransferredReplacementVar(final IReplacementVar pv, final TermTransferrer tt) {
			super(pv, tt);
			mDefinition = tt.transform(pv.getDefinition());
		}

		@Override
		public Term getDefinition() {
			return mDefinition;
		}
	}

}
