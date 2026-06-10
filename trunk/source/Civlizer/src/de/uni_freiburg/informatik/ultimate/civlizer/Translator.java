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

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.JoinStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogieOutput;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessInvariant;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.OwickiGriesAnnotation;

/**
 * Translates an Ultimate Boogie AST and its associated proof annotations into a CIVL program representation and write
 * the result in a file.
 *
 * <p>
 * This class traverses the Boogie abstract syntax tree (AST), extracts thread information, invariants, ghost variables,
 * and proof annotations, and generates the corresponding Civl code as a file.
 * </p>
 *
 * <p>
 * The translation process includes:
 * <ul>
 * <li>Declaration of thread identifiers and auxiliary types.</li>
 * <li>Generation of ghost variables from Owicki-Gries proofs.</li>
 * <li>Creation of thread control-flow procedures (fork, join, terminate).</li>
 * <li>Translation of Boogie declarations and procedures.</li>
 * <li>Insertion of yield invariants derived from witness annotations.</li>
 * </ul>
 * </p>
 *
 * <p>
 * The resulting CIVL program is returned as a string and can be used for subsequent verification steps.
 * </p>
 *
 * @author Gabriel Tréca (gabriel.treca@polytechnique.edu)
 */
public final class Translator extends BoogieVisitor {

	private final ProgramAndProof mProgramAndProof;
	private final StringBuilderWriter mWriter;
	private final BoogieOutput mOutput;

	/**
	 * Creates a translator for the specified program and proof. Preprocesses the input and initializes the output
	 * writer.
	 *
	 * @param programAndProof
	 *            the program and proof to translate
	 */
	public Translator(final ProgramAndProof programAndProof) {
		programAndProof.preprocess();
		mProgramAndProof = programAndProof;
		try {
			mWriter = new StringBuilderWriter();
		} catch (final IOException e) {
			throw new RuntimeException(e);
		}
		mOutput = new BoogieOutput(mWriter);
	}

	/**
	 * Translates the given Boogie program and proof into a Civl program.
	 *
	 * @param programAndProof
	 *            the Boogie program together with its proof annotations and thread information
	 * @return a string containing the generated Civl program
	 */
	public String translate() {

		addTidsType();

		addGhostVar();

		mWriter.println("var {:layer 0,2} {:linear} join_pool : Set (One Tid);\n");

		addThreadControlFlow();

		for (final Declaration elem : mProgramAndProof.getBoogieAst().getDeclarations()) {
			processDeclaration(elem);
		}

		return toString();
	}

	private void addStringList(final List<String> list, final String sep) {
		mWriter.print(String.join(sep, list));
	}

	private void addTidConst(final Tid tid) {
		mWriter.print("const unique const_");
		mWriter.print(tid.toString());
		mWriter.println(" : Tid;");
	}

	private void addTidsType() {

		mWriter.println("\ntype StartTid;");
		mWriter.println("const unique const_start_tid : StartTid;");
		mWriter.println("type Tid;");

		for (final Tid tid : mProgramAndProof.getTemplateVisitor().getTids()) {
			addTidConst(tid);
		}

		mWriter.print("\n");
	}

	private void addGhostVar() {
		for (final OwickiGriesAnnotation proof : mProgramAndProof.getProof()) {
			for (int i = 0; i < proof.getGhostVariables().size(); i++) {
				mWriter.print("var {:layer 2,2} ~ghost~");
				mWriter.print(String.valueOf(i));
				mWriter.print(" : int;\n\n"); // ??? TODO improve
			}
		}
	}

	private void addFork(final String procName) {
		mWriter.println("yield procedure {:layer 0} fork_" + procName + "({:linear_in} tid : One Tid);\n"
				+ "refines atomic action {:layer 1, 2} _ {}");
	}

	private void addTerminate() {
		mWriter.println("""
				yield procedure {:layer 0} terminate({:linear_in} tid : One Tid);
				refines atomic action {:layer 1, 2} _ {
					call One_Put(join_pool, tid);
				}
				""");
	}

	private void addJoin() {
		// linear_out try TODO
		mWriter.println("""
				yield procedure {:layer 0} join({:linear_out} tid : One Tid);
				refines atomic action {:layer 1, 2} _ {
					assume Set_Contains(join_pool, tid);
					call One_Get(join_pool, tid);
				}
				""");
	}

	private void addThreadControlFlow() {
		mWriter.print("\n");

		for (final String procName : mProgramAndProof.getTemplateVisitor().getAssociationTidMap().keySet()) {
			addFork(procName);
			mWriter.print("\n");
		}

		addTerminate();
		addJoin();
	}

	@Override
	public String toString() {
		return mWriter.toString();
	}

	@Override
	protected Declaration processDeclaration(final Declaration decl) {
		switch (decl) {
		case final Axiom axiom -> mOutput.printAxiom(axiom);
		case final ConstDeclaration constDecl -> mOutput.printConstDeclaration(constDecl);
		case final FunctionDeclaration funDecl -> visit(funDecl);
		case final Procedure proc -> visit(proc);
		case final TypeDeclaration typeDecl -> visit(typeDecl);
		case final VariableDeclaration varDecl -> {
			// this case is already handled by processVariableDeclaration

			// ???
			for (final VarList varl : varDecl.getVariables()) {

				final int len = varl.getIdentifiers().length;
				mWriter.print("var {:layer 0,2} ");

				for (int i = 0; i < len - 1; i++) {
					mWriter.print(varl.getIdentifiers()[i]);
					mWriter.print(", ");
				}

				mWriter.print(varl.getIdentifiers()[len - 1]);
				mWriter.print(" : ");
				mWriter.print(BoogiePrettyPrinter.print(varl.getType()));
				mWriter.print(";\n\n");
			}
		}
		}
		return decl;
	}

	private void addYieldInvariants(final String procName, final Expression annotation, final Statement statement,
			final Set<Tid> tidNeedsLinearity, final int counter) {

		mWriter.print("yield invariant {:layer 2} ");
		mWriter.print("yield_");
		mWriter.print(procName);
		mWriter.print("_");
		mWriter.print(Integer.toString(counter));

		mWriter.print("(");
		List<String> tids = new ArrayList<>();
		if ("ULTIMATE.start".equals(procName)) {
			tids.add("{:linear} start_tid : One StartTid");
		}

		for (final Tid tid : mProgramAndProof.getTemplateVisitor().getAllTidMap().getOrDefault(procName,
				Collections.emptyList())) {
			if (tidNeedsLinearity.contains(tid)) {
				tids.add("{:linear} " + tid.toString() + " : One Tid");
			} else {
				tids.add(" " + tid.toString() + " : One Tid");
			}
		}
		addStringList(tids, ", ");
		mWriter.println(");");

		mWriter.print("preserves ");
		tids = new ArrayList<>();
		if ("ULTIMATE.start".equals(procName)) {
			tids.add("start_tid->val == const_start_tid");
		}

		for (final Tid tid : mProgramAndProof.getTemplateVisitor().getAllTidMap().getOrDefault(procName,
				Collections.emptyList())) {
			tids.add(tid.toString() + "->val == const_" + tid.toString());
		}
		addStringList(tids, " && ");
		mWriter.print(";\n");

		if (annotation != null) {
			mWriter.print("preserves ");
			mWriter.print(BoogiePrettyPrinter.print(annotation));
			mWriter.print(";\n");
		}

		for (final Tid tid : mProgramAndProof.getTemplateVisitor().getAllTidMap().getOrDefault(procName,
				Collections.emptyList())) {
			final Optional<String> forked_proc = mProgramAndProof.getTemplateVisitor().getAssociationTidMap().entrySet()
					.stream().filter(entry -> entry.getValue().contains(tid)).map(Map.Entry::getKey).findFirst();

			if (forked_proc.isPresent() && !procName.equals(forked_proc.get())) {

				// TODO set at the end of the procedure
				final var initialLoc = mProgramAndProof.getIcfg().getProcedureExitNodes().get(forked_proc.get());
				final var invariant = (Expression) WitnessInvariant.getAnnotation(initialLoc).getInvariant();
				final var codeLocation = (BoogieLocation) ILocation.getAnnotation(initialLoc);

				mWriter.print("preserves ");
				mWriter.print("(Set_Contains(join_pool, " + tid.toString() + ")) ==> (");
				mWriter.print(BoogiePrettyPrinter.print(invariant));
				mWriter.print(");\n");
			}
		}

		mWriter.print("\n");
	}

	private void addNonAtomicStatement(final String procName, final Statement statement,
			final Set<Tid> tidNeedsLinearity, final int counter) {
		final List<String> arguments = new ArrayList<>();
		final List<String> returns = new ArrayList<>();

		if ("ULTIMATE.start".equals(procName)) {
			arguments.add("{:linear} start_tid : One StartTid");
		}

		for (final Tid tid : mProgramAndProof.getTemplateVisitor().getAllTidMap().getOrDefault(procName,
				Collections.emptyList())) {
			if (tidNeedsLinearity.contains(tid)) {
				arguments.add("{:linear} " + tid.toString() + " : One Tid");
			} else {
				arguments.add(tid.toString() + " : One Tid");
			}
		}

		for (final Map.Entry<String, ASTType> var : mProgramAndProof.getTemplateVisitor().getProcedureVariablesMap()
				.get(procName).entrySet()) {
			if (mProgramAndProof.getTemplateVisitor().getStatementParametersMap().get(statement.getLoc())
					.contains(var.getKey())) {
				arguments.add(var.getKey() + "_in : " + var.getValue());
				returns.add(var.getKey() + " : " + var.getValue());
			}
		}

		final BodyTransformer transformer = new BodyTransformer(mProgramAndProof);

		mWriter.print("yield procedure {:layer 2} ");
		mWriter.print(procName);
		mWriter.print("_stmt_");
		mWriter.print(Integer.toString(counter));

		mWriter.print("(");
		addStringList(arguments, ", ");
		mWriter.print(") returns (");
		addStringList(returns, ", ");
		mWriter.println(") {");

		if (statement instanceof final IfStatement ifStmt) {
			// Statement[] transformer.transformStatements(procName, ifStmt)
		} else if (statement instanceof final WhileStatement whileStmt) {
			// Statement[] transformer.transformStatements(procName, whileStmt)
		}

		mWriter.println("}\n");
	}

	private void addAtomicStatement(final String procName, final Statement statement, final int counter) {
		// IfStatement, ReturnStatement, CallStatement, WhileStatement, BreakStatement

		final List<String> arguments = new ArrayList<>();
		final List<String> returns = new ArrayList<>();

		for (final Map.Entry<String, ASTType> var : mProgramAndProof.getTemplateVisitor().getProcedureVariablesMap()
				.get(procName).entrySet()) {
			if (mProgramAndProof.getTemplateVisitor().getStatementParametersMap().get(statement.getLoc())
					.contains(var.getKey())) {
				arguments.add(var.getKey() + "_in : " + var.getValue());
				returns.add(var.getKey() + " : " + var.getValue());
			}
		}

		mWriter.print("yield procedure {:layer 0} ");
		mWriter.print(procName);
		mWriter.print("_stmt_");
		mWriter.print(Integer.toString(counter));

		mWriter.print("(");
		addStringList(arguments, ", ");
		mWriter.print(") returns (");
		addStringList(returns, ", ");
		mWriter.println(");");

		mWriter.println("refines atomic action {:layer 1,2} _ {");
		for (final String var : mProgramAndProof.getTemplateVisitor().getStatementParametersMap()
				.get(statement.getLoc())) {
			mWriter.print("    ");
			mWriter.print(var + " := " + var + "_in");
			mWriter.println(";");
		}

		if (statement instanceof final AtomicStatement atom) {
			for (final Statement stmt : atom.getBody()) {
				mWriter.println(BoogiePrettyPrinter.print(stmt));
			}
		} else {
			mWriter.println(BoogiePrettyPrinter.print(statement));
		}
		mWriter.println("}\n");
	}

	private void addStatement(final String procName, final Statement statement, final Set<Tid> tidNeedsLinearity,
			final int counter) {
		if (statement instanceof AssignmentStatement || statement instanceof AssertStatement
				|| statement instanceof AssumeStatement || statement instanceof HavocStatement
				|| statement instanceof AtomicStatement) {
			addAtomicStatement(procName, statement, counter);
		} else if (statement instanceof IfStatement || statement instanceof WhileStatement) {
			addNonAtomicStatement(procName, statement, tidNeedsLinearity, counter);
		}
	}

	void writeBody(final Procedure decl) {
		final BodyTransformer transformer = new BodyTransformer(mProgramAndProof);

		mOutput.printBody(transformer.transformBody(decl.getIdentifier(), decl.getBody()));
	}

	void writeProcedure(final Procedure decl) {
		final BodyTransformer transformer = new BodyTransformer(mProgramAndProof);

		mWriter.print("yield procedure {:layer 2} ");
		mWriter.print(decl.getIdentifier());

		mWriter.print("(");
		List<String> tids = new ArrayList<>();
		if ("ULTIMATE.start".equals(decl.getIdentifier())) {
			tids.add("{:linear} start_tid : One StartTid");
		}

		for (final Tid tid : mProgramAndProof.getTemplateVisitor().getAllTidMap().getOrDefault(decl.getIdentifier(),
				Collections.emptyList())) {
			tids.add("{:linear_in} " + tid.toString() + " : One Tid");
		}
		addStringList(tids, ", ");
		mWriter.println(")");

		mWriter.print("requires call yield_");
		mWriter.print(decl.getIdentifier());
		mWriter.print("_0");
		mWriter.print("(");
		tids = new ArrayList<>();
		if ("ULTIMATE.start".equals(decl.getIdentifier())) {
			tids.add("start_tid");
		}

		for (final Tid tid : mProgramAndProof.getTemplateVisitor().getAllTidMap().getOrDefault(decl.getIdentifier(),
				Collections.emptyList())) {
			tids.add(tid.toString());
		}
		addStringList(tids, ", ");
		mWriter.println(");");

		mWriter.println("{");

		writeBody(decl);

		mWriter.print("}\n\n");

		mWriter.flush(); // automatic flush ? TODO
	}

	@Override
	protected void visit(final Procedure decl) {
		// test
		final Map<ILocation, Expression> map = mProgramAndProof.getAnnotationMap(decl.getIdentifier());

		int counter = 0;
		final Set<Tid> tidNeedsLinearity = new HashSet<>(mProgramAndProof.getTemplateVisitor().getTids());
		Expression lastInvariant =
				mProgramAndProof.getTemplateVisitor().getEntryAnnotationMap().get(decl.getIdentifier());

		// initial invariant BEFORE first statement
		addYieldInvariants(decl.getIdentifier(), lastInvariant, null, tidNeedsLinearity, counter);

		counter++;

		// for (Statement statement : decl.getBody().getBlock()) {
		for (final Statement stmt : decl.getBody().getBlock()) {

			// skip return for now
			if (stmt instanceof ReturnStatement) {
				continue;
			}

			final Expression invariant = map.get(stmt.getLoc());
			if (invariant != null) {
				lastInvariant = invariant; // TODO handle conditional
			}
			/*
			 * final BoogieIcfgContainer loc = BoogieIcfgContainer.getAnnotation(stmt); final Expression invariant =
			 * (WitnessInvariant.getAnnotation(loc) == null) ? null : (Expression)
			 * WitnessInvariant.getAnnotation(loc).getInvariant();
			 */

			if (mProgramAndProof.getTemplateVisitor().containsGlobalVariables(stmt)) {
				addStatement(decl.getIdentifier(), stmt, tidNeedsLinearity, counter);
			}

			// ghost var update here

			System.out.println("TEST " + lastInvariant);
			System.out.println("TEST2 " + stmt);
			if (WitnessInvariant.getAnnotation(stmt) != null) {
				System.out.println("TEST3 " + WitnessInvariant.getAnnotation(stmt).getInvariant());
			}
			addYieldInvariants(decl.getIdentifier(), lastInvariant, stmt, tidNeedsLinearity, counter);

			if (stmt instanceof final JoinStatement joinstmt) {
				tidNeedsLinearity.add(new Tid(joinstmt.getThreadID()));
			}

			tidNeedsLinearity.clear();
			// tempory to make it work TODO
			if (mProgramAndProof.getTemplateVisitor().getAssociationTidMap().get(decl.getIdentifier()) != null) {
				tidNeedsLinearity
						.addAll(mProgramAndProof.getTemplateVisitor().getAssociationTidMap().get(decl.getIdentifier()));
			}
			counter++;
		}

		addYieldInvariants(decl.getIdentifier(),
				mProgramAndProof.getTemplateVisitor().getExitAnnotationMap().get(decl.getIdentifier()), null,
				tidNeedsLinearity, counter);

		writeProcedure(decl);
	}
}