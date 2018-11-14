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

package de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg;

import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermClassifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

/**
 * {@link SmtSymbols} contains axioms and SMT function symbols created throughout a toolchain.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class SmtSymbols {

	public static final int HARDCODED_SERIALNUMBER_FOR_AXIOMS = 0;

	private final IPredicate mAxioms;
	private final Map<String, SmtFunctionDefinition> mSmtFunctions2SmtFunctionDefinitions;

	/**
	 * Create an empty {@link SmtSymbols} instance.
	 */
	public SmtSymbols(final Script script) {
		this(script.term("true"), new String[0], Collections.emptyMap());
	}

	/**
	 * Create a {@link SmtSymbols} instance with axioms defined in a single term together with the procedures in which
	 * they were defined (if any), and a map from defined function names to {@link SmtFunctionDefinition} instances were
	 * each entry represents a defined SMT function.
	 */
	public SmtSymbols(final Term axioms, final String[] defininingProcedures,
			final Map<String, SmtFunctionDefinition> smtFun2SmtFunDef) {
		this(new BasicPredicate(HARDCODED_SERIALNUMBER_FOR_AXIOMS, defininingProcedures, axioms, Collections.emptySet(),
				axioms), smtFun2SmtFunDef);
	}

	/**
	 * Create a {@link SmtSymbols} instance with axioms defined by an {@link IPredicate} and a map from defined function
	 * names to {@link SmtFunctionDefinition} instances were each entry represents a defined SMT function.
	 */
	public SmtSymbols(final IPredicate axioms, final Map<String, SmtFunctionDefinition> smtFun2SmtFunDef) {
		mAxioms = Objects.requireNonNull(axioms);
		mSmtFunctions2SmtFunctionDefinitions = Objects.requireNonNull(smtFun2SmtFunDef);
		assert axioms.getClosedFormula() == axioms.getFormula() : "Axioms are not closed";
		assert axioms.getFormula().getFreeVars().length == 0 : "Axioms are not closed";
		assert axioms.getProcedures() != null;

	}

	/**
	 * Create a new {@link SmtSymbols} instance with an additional axiom without corresponding procedure.
	 *
	 * Also asserts the new axiom in the supplied script.
	 *
	 */
	public SmtSymbols addAxiom(final Script script, final Term additionalAxioms) {
		final Term newAxioms = SmtUtils.and(script, mAxioms.getClosedFormula(), additionalAxioms);
		final LBool quickCheckAxioms = script.assertTerm(additionalAxioms);
		assert quickCheckAxioms != LBool.UNSAT : "Axioms are inconsistent";
		final IPredicate newAxiomsPred = new BasicPredicate(HARDCODED_SERIALNUMBER_FOR_AXIOMS, new String[0],
				additionalAxioms, Collections.emptySet(), newAxioms);
		return new SmtSymbols(newAxiomsPred, mSmtFunctions2SmtFunctionDefinitions);
	}

	/**
	 * Create a new {@link SmtSymbols} instance with an additional function declaration.
	 *
	 * Also define the function in the supplied script.
	 *
	 */
	public SmtSymbols addFunction(final Script script, final SmtFunctionDefinition additionalFunction) {
		final Map<String, SmtFunctionDefinition> map = new LinkedHashMap<>(mSmtFunctions2SmtFunctionDefinitions);
		map.put(additionalFunction.getName(), additionalFunction);
		additionalFunction.defineOrDeclareFunction(script);
		return new SmtSymbols(mAxioms, map);
	}

	/**
	 * Define all symbols defined by this SmtSymbols in a fresh script (by asserting or defining)
	 *
	 * @param script
	 *            the new script.
	 */
	public void transferSymbols(final Script script) {
		final TermTransferrer tt = new TermTransferrer(script);
		final LBool quickCheckAxioms = script.assertTerm(tt.transform(mAxioms.getClosedFormula()));
		assert quickCheckAxioms != LBool.UNSAT : "Axioms are inconsistent";
		for (final Entry<String, SmtFunctionDefinition> entry : mSmtFunctions2SmtFunctionDefinitions.entrySet()) {
			entry.getValue().defineOrDeclareFunction(script, tt);
		}

	}

	/**
	 * Apply a {@link TermClassifier} to all axioms and function bodies defined by this {@link SmtSymbols} instance.
	 */
	public void classify(final TermClassifier cs) {
		cs.checkTerm(mAxioms.getFormula());
		for (final Entry<String, SmtFunctionDefinition> entry : mSmtFunctions2SmtFunctionDefinitions.entrySet()) {
			if (entry.getValue().getDefinition() == null) {
				continue;
			}
			cs.checkTerm(entry.getValue().getDefinition());
		}
	}

	/**
	 * Replace all function applications of the supplied term that are contained in this {@link SmtSymbols} instance
	 * with their bodies.
	 *
	 * TODO: Also inline axioms.
	 */
	public Term inline(final Script script, final Term term) {
		return new SmtFunctionInliner().inline(script, term);
	}

	public IPredicate getAxioms() {
		return mAxioms;
	}

	/**
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	private class SmtFunctionInliner extends TermTransformer {

		private Script mScript;

		public Term inline(final Script script, final Term term) {
			mScript = script;
			return transform(term);
		}

		@Override
		public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs) {
			final String funName = appTerm.getFunction().getName();
			final SmtFunctionDefinition decl = mSmtFunctions2SmtFunctionDefinitions.get(funName);
			if (decl == null) {
				super.convertApplicationTerm(appTerm, newArgs);
				return;
			}
			final Term body = decl.getDefinition();
			if (body == null) {
				super.convertApplicationTerm(appTerm, newArgs);
				return;
			}
			if (appTerm.getParameters().length == 0) {
				setResult(body);
				return;
			}

			final Term[] paramVars = decl.getParamVars();
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
			setResult(new Substitution(mScript, substitutionMapping).transform(body));
		}
	}

}
