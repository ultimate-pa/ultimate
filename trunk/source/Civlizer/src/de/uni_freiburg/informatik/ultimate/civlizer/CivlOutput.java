/*
 * Copyright (C) 2026 Dominik Klumpp (klumpp@lix.polytechnique.fr)
 * Copyright (C) 2026 École Polytechnique
 *
 * This file is part of the ULTIMATE Civlizer plug-in.
 *
 * The ULTIMATE Civlizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Civlizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Civlizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Civlizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Civlizer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.civlizer;

import java.io.PrintWriter;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogieOutput;
import de.uni_freiburg.informatik.ultimate.civlizer.model.AnonymousAction;
import de.uni_freiburg.informatik.ultimate.civlizer.model.BoogieDeclaration;
import de.uni_freiburg.informatik.ultimate.civlizer.model.CivlDeclaration;
import de.uni_freiburg.informatik.ultimate.civlizer.model.CivlProgram;
import de.uni_freiburg.informatik.ultimate.civlizer.model.ParameterDeclaration;
import de.uni_freiburg.informatik.ultimate.civlizer.model.ParameterDeclaration.Linearity;
import de.uni_freiburg.informatik.ultimate.civlizer.model.YieldInvariant;
import de.uni_freiburg.informatik.ultimate.civlizer.model.YieldProcedure;

/**
 * Writes pretty-printed representations of Civl AST nodes to an output stream.
 *
 * @author Dominik Klumpp (klumpp@lix.polytechnique.fr)
 */
public class CivlOutput implements AutoCloseable {
	private final PrintWriter mWriter;
	private final BoogieOutput mBoogieOutput;

	public CivlOutput(final PrintWriter output) {
		mWriter = output;
		mBoogieOutput = new CivlizedBoogieOutput(output);
	}

	public void print(final CivlProgram program) {
		boolean first = true;
		for (final var decl : program.getDeclarations()) {
			if (!first) {
				mWriter.println();
			}
			print(decl);
			first = false;
		}
	}

	public void print(final CivlDeclaration decl) {
		switch (decl) {
		case final BoogieDeclaration bdecl -> printBoogieDeclaration(bdecl.getDecl());
		case final YieldProcedure proc -> printYieldProcedure(proc);
		case final YieldInvariant inv -> printYieldInvariant(inv);
		}
	}

	public void printYieldInvariant(final YieldInvariant inv) {
		mWriter.print("yield invariant ");
		mBoogieOutput.printAttributes(CivlUtils.createLayerAttribute(inv.getIntroductionLayer()));
		mWriter.print(" ");
		mWriter.print(inv.getIdentifier());
		mWriter.print("(");
		print(inv.getParams());
		mWriter.println(");");

		for (final var preserves : inv.getPreserves()) {
			mWriter.print("preserves ");
			mBoogieOutput.printExpression(preserves);
			mWriter.println(";");
		}
	}

	public void printYieldProcedure(final YieldProcedure proc) {
		mWriter.print("yield procedure ");
		mBoogieOutput.printAttributes(CivlUtils.createLayerAttribute(proc.getDisappearingLayer()));
		mWriter.print(" ");
		mWriter.print(proc.getIdentifier());
		mWriter.print("(");
		print(proc.getInParams());
		mWriter.print(")");

		if (proc.getOutParams().length > 0) {
			mWriter.print(" returns (");
			print(proc.getOutParams());
			mWriter.print(")");
		}

		if (proc.getBody() == null) {
			mWriter.print(";");
		}
		mWriter.println();

		for (final var requires : proc.getRequires()) {
			mWriter.print("requires ");
			mBoogieOutput.printStatement(requires);
		}

		for (final var ensures : proc.getEnsures()) {
			mWriter.print("ensures ");
			mBoogieOutput.printStatement(ensures);
		}

		if (proc.getBody() != null) {
			mWriter.println("{");
			mBoogieOutput.printBody(proc.getBody());
			mWriter.println("}");
		}

		if (proc.getRefines() != null) {
			mWriter.print("refines ");
			print(proc.getRefines());
		}
	}

	public void print(final AnonymousAction refines) {
		mWriter.print("atomic action ");

		mBoogieOutput.printAttributes(
				CivlUtils.createLayerAttribute(refines.getIntroductionLayer(), refines.getDisappearingLayer()));

		mWriter.println(" _");

		mWriter.println("{");
		mBoogieOutput.printBody(refines.getBody());
		mWriter.println("}");
	}

	private void print(final ParameterDeclaration[] parameterList) {
		for (int i = 0; i < parameterList.length; ++i) {
			if (i > 0) {
				mWriter.print(", ");
			}
			print(parameterList[i]);
		}
	}

	private void print(final ParameterDeclaration parameter) {
		if (parameter.getLinearity() != Linearity.NONE) {
			final var linearityAttribute = CivlUtils.createLinearityAttribute(parameter.getLinearity());
			mBoogieOutput.printAttributes(linearityAttribute);
			mWriter.print(" ");
		}
		mWriter.print(parameter.getIdentifier());
		mWriter.print(" : ");

		mBoogieOutput.printType(parameter.getType());
	}

	private void printBoogieDeclaration(final Declaration decl) {
		switch (decl) {
		case final Axiom a -> mBoogieOutput.printAxiom(a);
		case final ConstDeclaration c -> mBoogieOutput.printConstDeclaration(c);
		case final FunctionDeclaration f -> mBoogieOutput.printFunctionDeclaration(f);
		case final TypeDeclaration t -> mBoogieOutput.printTypeDeclaration(t);
		case final VariableDeclaration v -> mBoogieOutput.printVariableDeclaration(v);
		case final Procedure p -> {
			assert false : "Unexpected Boogie procedure in Civl program";
		}
		}
	}

	@Override
	public void close() {
		mBoogieOutput.close();
		mWriter.close();
	}

	private static final class CivlizedBoogieOutput extends BoogieOutput {
		public CivlizedBoogieOutput(final PrintWriter output) {
			super(output);
		}

		@Override
		protected void printExpression(final Expression expr, final int precedence) {
			// Civl uses '->' instead of '!' to access members of data types.
			if (expr instanceof final StructAccessExpression saexpr) {
				if (precedence > PRECEDENCE_ACCESS) {
					mWriter.print("(");
				}
				printExpression(saexpr.getStruct(), PRECEDENCE_ACCESS);
				mWriter.print("->");
				mWriter.print(saexpr.getField());
				if (precedence > PRECEDENCE_ACCESS) {
					mWriter.print(")");
				}
				return;
			}

			// For all other expressions, rely on the default behaviour of BoogieOutput.
			super.printExpression(expr, precedence);
		}

		@Override
		protected void printLHS(final LeftHandSide lhs) {
			// Civl uses '->' instead of '!' to access members of data types.
			if (lhs instanceof final StructLHS strlhs) {
				printLHS(strlhs.getStruct());
				mWriter.print("->");
				mWriter.print(strlhs.getField());
				return;
			}
			super.printLHS(lhs);
		}

		@Override
		public void printSpecification(final Specification spec) {
			// Civl loop invariants can use calls to yield invariants, and the { :yields } attribute.
			if (spec instanceof final LoopInvariantSpecification invariant) {
				if (invariant.isFree()) {
					mWriter.print("free ");
				}
				mWriter.print("invariant ");
				switch (invariant.getFormula()) {
				case final BooleanLiteral literal:
					mWriter.print("{ :yields } ");
					break;
				default:
					mWriter.print("call ");
				}
				printExpression(invariant.getFormula());
				mWriter.println(";");
				return;
			}

			// For all other specifications, rely on the default behaviour of BoogieOutput.
			super.printSpecification(spec);
		}
	}
}
