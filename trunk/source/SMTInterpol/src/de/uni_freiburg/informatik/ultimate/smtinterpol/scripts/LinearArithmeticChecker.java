/*
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.scripts;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.NoopScript;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;

/**
 * Script to check a SMT-LIB benchmark for non-linear arithmetic.  This script can
 * be used with
 *
 * <pre>
 * java -jar smtinterpol.jar -script LinearArithmeticChecker -o regular-output-channel=/dev/null benchmark.smt2
 * </pre>
 *
 * You can also check multiple scripts by creating a file like:
 * <pre>
 * (echo "bench1.smt2")
 * (include "bench1.smt2")
 * (reset)
 * (echo "bench2.smt2")
 * (include "bench2.smt2")
 * (reset)
 * </pre>
 * in which case the script prints the string from the last echo, if the benchmark did contain non-linear arithmetic.
 *
 * @author Jochen Hoenicke
 */
public class LinearArithmeticChecker extends NoopScript {
	FormulaUnLet mUnletter = new FormulaUnLet();
	LinearChecker mChecker = new LinearChecker();
	long mNumProblems = 0;
	String mEchoString = "";

	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException {
		mChecker.transform(mUnletter.transform(term));
		return super.assertTerm(term);
	}

	@Override
	public QuotedObject echo(QuotedObject msg) {
		mEchoString = msg.getValue();
		return super.echo(msg);
	}

	@Override
	public void reset() {
		if (mNumProblems > 0) {
			System.err.println("Found " + mNumProblems + " problems.");
			System.out.println(mEchoString);
			mNumProblems = 0;
		}
		super.reset();
	}

	@Override
	public void exit() {
		if (mNumProblems > 0) {
			System.err.println("Found " + mNumProblems + " problems.");
			System.exit(1);
		}
		super.exit();
	}

	class LinearChecker extends TermTransformer {
		@Override
		public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
			FunctionSymbol fs = appTerm.getFunction();
			if (fs.isIntern()) {
				switch (fs.getName()) {
				case "abs":
				case "mod":
				case "div":
					System.err.println("Non-linear function " + fs.getName() + " in benchmark");
					mNumProblems++;
					break;
				case "*": {
					Term leftArg = SMTAffineTerm.parseConstant(newArgs[0]);
					Term rightArg = SMTAffineTerm.parseConstant(newArgs[1]);
					if (newArgs.length != 2
							|| (!(leftArg instanceof ConstantTerm) && !(rightArg instanceof ConstantTerm))) {
						System.err.println("Non-linear term " + appTerm);
						mNumProblems++;
					}
					break;
				}
				case "/": {
					Term constant = SMTAffineTerm.parseConstant(appTerm);
					if (!(constant instanceof ConstantTerm)) {
						System.err.println("Non-constant division: " + appTerm);
						mNumProblems++;
					}
					break;
				}
				default:
					break;
				}
			}
			super.convertApplicationTerm(appTerm, newArgs);
		}
	}
}
