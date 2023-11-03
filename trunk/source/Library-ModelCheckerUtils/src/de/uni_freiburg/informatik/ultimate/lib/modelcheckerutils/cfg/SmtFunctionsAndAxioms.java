/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.DeclarableFunctionSymbol;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.ISmtDeclarable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.NonDeclaringTermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;

/**
 * {@link SmtFunctionsAndAxioms} contains axioms and SMT function symbols
 * created throughout a toolchain.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 *         TODO: Extend {@link HistoryRecordingScript} to be able to create a
 *         nicer term transferrer
 *
 *         TODO 20220401 Matthias: It does not make sense to store axioms and
 *         SMT function symbols that are created throughout a toolchain in the
 *         ICFG. Each algorithm should store the function symbol that it
 *         utilizes. FunctionSymbols that are utilized by the ICFG should be
 *         stored in the symbol table of the ICFG.
 *
 */
public class SmtFunctionsAndAxioms {

	public static final int HARDCODED_SERIALNUMBER_FOR_AXIOMS = 0;

	/**
	 * {@link Script} instance that was used to create the ICFG to which this {@link SmtFunctionsAndAxioms} instance
	 * belongs.
	 */
	private final HistoryRecordingScript mScript;
	private final ManagedScript mMgdScript;
	private final IPredicate mAxioms;

	/**
	 * Create a {@link SmtFunctionsAndAxioms} instance with no axioms.
	 *
	 * @param mgdScript
	 *            A {@link ManagedScript} instance that was used to build the ICFG to which this
	 *            {@link SmtFunctionsAndAxioms} instance belongs.
	 */
	public SmtFunctionsAndAxioms(final ManagedScript mgdScript) {
		this(mgdScript.getScript().term("true"), Collections.emptySet(), mgdScript);
	}

	/**
	 * Create a {@link SmtFunctionsAndAxioms} instance with axioms defined by a
	 * {@link Term} and a set of {@link IProgramFunction}s.
	 *
	 * @param axioms Axioms given as {@link Term}.
	 * @param funs   The procedures from which the axioms come or null.
	 * @param script A {@link ManagedScript} instance that was used to build the
	 *               axioms term and the ICFG to which this
	 *               {@link SmtFunctionsAndAxioms} instance belongs.
	 */
	public SmtFunctionsAndAxioms(final Term axioms, final Set<IProgramFunction> funs,
			final ManagedScript mgdScript) {
		this(new BasicPredicate(HARDCODED_SERIALNUMBER_FOR_AXIOMS, new String[0], axioms, Collections.emptySet(), funs,
				axioms), mgdScript);
	}

	/**
	 * Create a {@link SmtFunctionsAndAxioms} instance.
	 *
	 * @param axioms
	 *            Axioms given as {@link IPredicate}
	 * @param script
	 *            A {@link ManagedScript} instance that was used to build the axioms and the ICFG to which this
	 *            {@link SmtFunctionsAndAxioms} instance belongs.
	 */
	public SmtFunctionsAndAxioms(final IPredicate axioms, final ManagedScript mgdScript) {
		mAxioms = Objects.requireNonNull(axioms);
		mMgdScript = mgdScript;
		mScript = Objects.requireNonNull(
				HistoryRecordingScript.extractHistoryRecordingScript(Objects.requireNonNull(mgdScript.getScript())));
		assert axioms.getClosedFormula() == axioms.getFormula() : "Axioms are not closed";
		assert axioms.getFormula().getFreeVars().length == 0 : "Axioms are not closed";
		assert axioms.getProcedures() != null;

	}

	/**
	 * Create a new {@link SmtFunctionsAndAxioms} instance with an additional axiom without corresponding procedure.
	 * Also asserts the new axiom in the underlying script.
	 * @param symbolTable
	 */
	public SmtFunctionsAndAxioms addAxiom(final Term additionalAxioms, final IIcfgSymbolTable symbolTable) {
		final Term newAxioms = SmtUtils.and(mScript, mAxioms.getClosedFormula(), additionalAxioms);
		final LBool quickCheckAxioms = mScript.assertTerm(additionalAxioms);
		// TODO: Use an Ultimate result to report inconsistent axioms; we do not want to disallow inconsistent axioms,
		// we just want to be informed about them.
		assert quickCheckAxioms != LBool.UNSAT : "Axioms are inconsistent";
		final TermVarsProc tvp = TermVarsProc.computeTermVarsProc(newAxioms, mMgdScript, symbolTable);
		final IPredicate newAxiomsPred = new BasicPredicate(HARDCODED_SERIALNUMBER_FOR_AXIOMS, tvp.getProcedures(),
				tvp.getFormula(), tvp.getVars(), tvp.getFuns(), tvp.getClosedFormula());
		return new SmtFunctionsAndAxioms(newAxiomsPred, mMgdScript);
	}

	// TODO: We also want a transfer function that transfers only some variables s.t. trace checks can be more focused

	/**
	 * Define all symbols defined by the underlying {@link Script} instance of this {@link SmtFunctionsAndAxioms}
	 * instance in a fresh script and assert all Axioms there.
	 *
	 * @param script
	 *            the fresh script.
	 */
	public void transferAllSymbols(final Script script) {
		HistoryRecordingScript.transferHistoryFromRecord(mScript, script);

		final NonDeclaringTermTransferrer tt = new NonDeclaringTermTransferrer(script);
		final Term transferredAxiom = tt.transform(mAxioms.getClosedFormula());
		if (!SmtUtils.isTrueLiteral(transferredAxiom)) {
			final LBool quickCheckAxioms = script.assertTerm(transferredAxiom);
			// TODO: Use an Ultimate result to report inconsistent axioms; we do not want to disallow inconsistent
			// axioms,
			// we just want to be informed about them.
			assert quickCheckAxioms != LBool.UNSAT : "Axioms are inconsistent";
		}
	}

	/**
	 * Replace all function applications of the supplied term that are contained in this {@link SmtFunctionsAndAxioms}
	 * instance with their bodies.
	 *
	 * TODO: Also inline axioms.
	 */
	public Term inline(final Term term) {
		return new SmtFunctionInliner().inline(mMgdScript, term);
	}

	public IPredicate getAxioms() {
		return mAxioms;
	}

	/**
	 * @return A map from function name to function definition containing all functions with a body of the enclosed
	 *         script.
	 */
	public Map<String, DeclarableFunctionSymbol> getDefinedFunctions() {
		return mScript.getSymbolTable().entrySet().stream()
				.filter(a -> a.getValue() instanceof DeclarableFunctionSymbol)
				.map(a -> (DeclarableFunctionSymbol) a.getValue()).filter(a -> a.getDefinition() != null)
				.collect(Collectors.toMap(DeclarableFunctionSymbol::getName, a -> a));
	}

	/**
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	private static class SmtFunctionInliner extends TermTransformer {

		private ManagedScript mMgdScript;
		private HistoryRecordingScript mScript;

		public Term inline(final ManagedScript mgdScript, final Term term) {
			mMgdScript = mgdScript;
			mScript = HistoryRecordingScript.extractHistoryRecordingScript(mgdScript.getScript());
			if (mScript == null) {
				throw new IllegalArgumentException(
						mgdScript.getScript().getClass() + " does not contain a " + HistoryRecordingScript.class);
			}
			return transform(term);
		}

		@Override
		public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs) {
			final String funName = appTerm.getFunction().getName();
			final ISmtDeclarable decl = mScript.getSymbolTable().get(funName);
			if (decl == null) {
				setResult(SmtUtils.convertApplicationTerm(appTerm, newArgs, mScript));
				return;
			}
			assert decl instanceof DeclarableFunctionSymbol;
			final DeclarableFunctionSymbol funDecl = (DeclarableFunctionSymbol) decl;
			final Term body = funDecl.getDefinition();
			if (body == null) {
				setResult(SmtUtils.convertApplicationTerm(appTerm, newArgs, mScript));
				return;
			}
			if (appTerm.getParameters().length == 0) {
				setResult(body);
				return;
			}

			final Term[] paramVars = funDecl.getParamVars();
			assert newArgs.length == paramVars.length;
			final Map<Term, Term> substitutionMapping = new HashMap<>();
			for (int i = 0; i < paramVars.length; ++i) {
				final Term paramVar = paramVars[i];
				if (paramVar == null) {
					// this var does not occur in the body
					continue;
				}
				substitutionMapping.put(paramVar, newArgs[i]);
			}
			setResult(Substitution.apply(mMgdScript, substitutionMapping, body));
		}
	}

}
