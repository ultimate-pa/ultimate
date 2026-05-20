
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
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BreakStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.JoinStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Trigger;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogieOutput;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessInvariant;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.OwickiGriesAnnotation;

public final class Translator extends BoogieVisitor {

	private ProgramAndProof mProgramAndProof;
	private StringBuilderWriter mWriter;
	private BoogieOutput mOutput;

	Translator(ProgramAndProof programAndProof) {
		programAndProof.preprocess();
		mProgramAndProof = programAndProof;
		try {
			mWriter = new StringBuilderWriter();
		}
		catch (IOException e) {
            throw new RuntimeException(e);
        }
		mOutput = new BoogieOutput(mWriter);
	}

	/**
	 * translate the Ultimate boogie Ast into a String representing the resulting Civl program
	 */
	public static String translate(ProgramAndProof programAndProof) {
		Translator translation = new Translator(programAndProof);

		translation.addTidsType();

		translation.addGhostVar();

		translation.mWriter.println("var {:layer 0,2} {:linear} join_pool : Set (One Tid);\n");

		translation.addThreadControlFlow();

		for (Declaration elem : programAndProof.getBoogieAst().getDeclarations()) {
			translation.processDeclaration(elem);
        }

		return translation.toString();
	}

	private void addStringList(List<String> list, String sep) {
		mWriter.print(String.join(sep, list));
	}

	private void addTidConst(Tid tid) {
		mWriter.print("const unique const_");
		mWriter.print(tid.toString());
		mWriter.println(" : Tid;");
	}

	private void addTidsType() {
		
		mWriter.println("\ntype StartTid;");
		mWriter.println("const unique const_start_tid : StartTid;");
		mWriter.println("type Tid;");

		for (Tid tid : mProgramAndProof.getTemplateVisitor().getTids()) {
			addTidConst(tid);
		}

		mWriter.print("\n");
	}

	private void addGhostVar() {
		for (OwickiGriesAnnotation proof : mProgramAndProof.getProof()) {
			for (int i = 0; i < proof.getGhostVariables().size(); i++) {
				mWriter.print("var {:layer 1,2} ~ghost~");
				mWriter.print(String.valueOf(i));
				mWriter.print(" : int;\n\n"); // ??? TODO
			}
		}
	}

	private void addFork(String procName) {
		mWriter.println("yield procedure {:layer 2} fork_" + procName + 
		"({:linear} start_tid : One StartTid, {:linear_in} tid : One Tid) {}");
	}

	private void addTerminate() {
		mWriter.println(
			"""
			yield procedure {:layer 0} terminate({:linear_in} tid : One Tid);
			refines atomic action {:layer 1, 2} _ {
				call One_Put(join_pool, tid);
			}
			"""
		);
	}

	private void addJoin() {
		// linear_out try TODO
		mWriter.println(
			"""
			yield procedure {:layer 0} join(
				{:linear} start_tid : One StartTid, 
				{:linear_out} tid : One Tid);
			refines atomic action {:layer 1, 2} _ {
				assume Set_Contains(join_pool, tid);
				call One_Get(join_pool, tid);
			}
			"""
		);
	}

	private void addThreadControlFlow() {
		mWriter.print("\n");

		for (String procName : mProgramAndProof.getTemplateVisitor().getAssociationTidMap().keySet()) {
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
				for (VarList varl : varDecl.getVariables()) {

					int len = varl.getIdentifiers().length;
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

	private void addYieldInvariants(
			final String procName, 
			final Expression annotation, 
			final Statement statement, 
			Set<Tid> currentForkedTid, 
			int counter) {

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

		for (Tid tid : mProgramAndProof
			.getTemplateVisitor()
			.getAllTidMap()
			.getOrDefault(procName, Collections.emptyList()))
		{
			if (currentForkedTid
				.contains(tid)) {
				tids.add(" " + tid.toString() + " : One Tid");
			}
			else {
				tids.add("{:linear} " + tid.toString() + " : One Tid");
			}
		}
		addStringList(tids, ", ");
		mWriter.println(");");


		mWriter.print("preserves ");
		tids = new ArrayList<>();
		if ("ULTIMATE.start".equals(procName)) {
			tids.add("start_tid->val == const_start_tid");
		}
		
		for (Tid tid : mProgramAndProof
			.getTemplateVisitor()
			.getAllTidMap()
			.getOrDefault(procName, Collections.emptyList()))
		{
			tids.add(tid.toString() + "->val == const_" + tid.toString());
		}
		addStringList(tids, " && ");
		mWriter.print(";\n");

		if (annotation != null) {
			mWriter.print("preserves ");
			mWriter.print(BoogiePrettyPrinter.print(annotation));
			mWriter.print(";\n");
		}
		else {
			// requirement
			final var initialLoc = mProgramAndProof
				.getIcfg()
				.getProcedureEntryNodes()
				.get(procName);
			if (WitnessInvariant.getAnnotation(initialLoc) != null) {
				final var invariant = (Expression) WitnessInvariant.getAnnotation(initialLoc).getInvariant();
				final var codeLocation = (BoogieLocation) ILocation.getAnnotation(initialLoc);

				if (invariant != null) {
					mWriter.print("preserves ");
					mWriter.print(BoogiePrettyPrinter.print(invariant));
					mWriter.print(";\n");
				}
			}
		}

		for (Tid tid : currentForkedTid) {
			final Optional<String> forked_proc = mProgramAndProof
				.getTemplateVisitor()
				.getAssociationTidMap().entrySet().stream()
				.filter(entry -> entry.getValue().contains(tid))
				.map(Map.Entry::getKey)
				.findFirst();

			if (forked_proc.isPresent()) {
				
				// TODO set at the end of the procedure
				final var initialLoc = mProgramAndProof
					.getIcfg()
					.getProcedureExitNodes()
					.get(forked_proc.get());
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

	private void addAtomicStatement(String procName, final Statement statement, int counter) {
		if (statement instanceof AssertStatement 
            || statement instanceof AssignmentStatement
            || statement instanceof AssumeStatement
            || statement instanceof HavocStatement
            || statement instanceof AtomicStatement) {
				mWriter.print("yield procedure {:layer 0} ");
				mWriter.print(procName);
				mWriter.print("_stmt_");
				mWriter.print(Integer.toString(counter));
				mWriter.println("();");

				mWriter.println("refines atomic action {:layer 1,2} _ {");
				mWriter.print("    ");
				mWriter.println(BoogiePrettyPrinter.print(statement));
				mWriter.println("}\n");
		}
	}

	@Override
	protected void visit(final Procedure decl) {
		
		Map<ILocation, Expression> annotationMap = mProgramAndProof.getAnnotationMap(decl.getIdentifier());
		/* Write invariant and atomic */
		int counter = 0;
		Set<Tid> currentForkedTid = new HashSet<>();

		// initial invariant BEFORE first statement
		addYieldInvariants(
			decl.getIdentifier(),
			null,
			null,
			currentForkedTid,
			counter
		);

		counter++;

		//for (Statement statement : decl.getBody().getBlock()) {
		for (int i = 0; i < decl.getBody().getBlock().length; i++) {
			// WHY ???

			if (i < decl.getBody().getBlock().length - 1) {
				if (decl.getBody().getBlock()[i+1] instanceof final ForkStatement forkstmt) {
				currentForkedTid.add(new Tid(forkstmt.getThreadID()));
				}
				else if (decl.getBody().getBlock()[i+1] instanceof final JoinStatement joinstmt) {
					currentForkedTid.remove(new Tid(joinstmt.getThreadID()));
				}
			}

			addAtomicStatement(
				decl.getIdentifier(),
				decl.getBody().getBlock()[i],
				counter - 1
			);

			Expression annotation =
				annotationMap.get(decl.getBody().getBlock()[i].getLoc());

			addYieldInvariants(
				decl.getIdentifier(),
				annotation,
				decl.getBody().getBlock()[i],
				currentForkedTid,
				counter
			);

			counter++;
		}

		/* Write the yield procedure itself */
		//if (decl.getInParams() != null || decl.getOutParams() != null) {
		//	System.err.println("fatal procedure take no parameter for now");
		//	System.exit(1);
		//}

		/* Write Thread template */
		BodyTransformer transformer = new BodyTransformer(mProgramAndProof);

		mWriter.print("yield procedure {:layer 2} ");
		mWriter.print(decl.getIdentifier());

		mWriter.print("("); 
		List<String> tids = new ArrayList<>();
		if ("ULTIMATE.start".equals(decl.getIdentifier())) {
			tids.add("{:linear} start_tid : One StartTid");
		}

		for (Tid tid : mProgramAndProof
			.getTemplateVisitor()
			.getAllTidMap()
			.getOrDefault(decl.getIdentifier(), Collections.emptyList()))
		{
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

		for (Tid tid : mProgramAndProof
			.getTemplateVisitor()
			.getAllTidMap()
			.getOrDefault(decl.getIdentifier(), Collections.emptyList()))
		{
			tids.add(tid.toString());
		}
		addStringList(tids, ", ");
		mWriter.println(");");


		mWriter.println("{");

		// for (VariableDeclaration varDecl : decl.getBody().getLocalVars()) {
		//	mWriter.print(BoogiePrettyPrinter.print(varDecl));
		// }
		mWriter.print("\n");
		mOutput.printBody(transformer.transformBody(decl.getIdentifier(), decl.getBody()));
		mWriter.print("}\n\n");

		mWriter.flush(); // automatic flush ? TODO
	}

	protected void visit(final TypeDeclaration decl) {
		// empty because it may be overridden (but does not have to)
	}

	@Override
	protected ASTType processType(final ASTType type) {
		switch (type) {
		case final ArrayType array -> visit(array);
		case final NamedType named -> visit(named);
		case final PrimitiveType primitive -> visit(primitive);
		case final StructType struct -> visit(struct);
		}
		return type;
	}

	protected void visit(final ArrayType type) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final NamedType type) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final PrimitiveType type) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final StructType type) {
		// empty because it may be overridden (but does not have to)
	}

	@Override
	protected Statement processStatement(final Statement statement) {
		switch (statement) {
		case final AssertStatement assertStmt -> visit(assertStmt);
		case final AssignmentStatement assignStmt -> visit(assignStmt);
		case final AssumeStatement assumeStmt -> visit(assumeStmt);
		case final AtomicStatement atomicStmt -> visit(atomicStmt);
		case final BreakStatement breakStmt -> visit(breakStmt);
		case final CallStatement callStmt -> visit(callStmt);
		case final ForkStatement forkStmt -> visit(forkStmt);
		case final GotoStatement gotoStmt -> visit(gotoStmt);
		case final HavocStatement havocStmt -> visit(havocStmt);
		case final IfStatement ifStmt -> visit(ifStmt);
		case final JoinStatement joinStmt -> visit(joinStmt);
		case final Label label -> visit(label);
		case final ReturnStatement returnStmt -> visit(returnStmt);
		case final WhileStatement whileStmt -> visit(whileStmt);
		}
		return statement;
	}

	protected void visit(final WhileStatement statement) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final AtomicStatement statment) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final ReturnStatement statement) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final Label statement) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final IfStatement statement) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final HavocStatement statement) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final GotoStatement statement) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final CallStatement statement) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final ForkStatement statement) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final JoinStatement statement) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final BreakStatement statement) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final AssignmentStatement statement) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final AssumeStatement statement) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final AssertStatement statement) {
		// empty because it may be overridden (but does not have to)
	}

	@Override
	protected LeftHandSide processLeftHandSide(final LeftHandSide lhs) {
		switch (lhs) {
		case final ArrayLHS array -> visit(array);
		case final StructLHS struct -> visit(struct);
		case final VariableLHS variable -> visit(variable);
		}
		return lhs;
	}

	protected void visit(final VariableLHS lhs) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final StructLHS lhs) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final ArrayLHS lhs) {
		// empty because it may be overridden (but does not have to)
	}

	@Override
	protected Specification processSpecification(final Specification spec) {
		switch (spec) {
		case final EnsuresSpecification ensures -> visit(ensures);
		case final LoopInvariantSpecification loopInvariant -> visit(loopInvariant);
		case final ModifiesSpecification modifies -> visit(modifies);
		case final RequiresSpecification requires -> visit(requires);
		}
		return spec;
	}

	protected void visit(final RequiresSpecification spec) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final ModifiesSpecification spec) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final LoopInvariantSpecification spec) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final EnsuresSpecification spec) {
		// empty because it may be overridden (but does not have to)
	}

	@Override
	protected <T extends Attribute> T processAttribute(final T attr) {
		switch (attr) {
		case final NamedAttribute named -> visit(named);
		case final Trigger trigger -> visit(trigger);
		}
		return attr;
	}

	protected void visit(final NamedAttribute attr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final Trigger attr) {
		// empty because it may be overridden (but does not have to)
	}

	@Override
	protected Expression processExpression(final Expression expr) {
		switch (expr) {
		case final ArrayAccessExpression arrayAccess -> visit(arrayAccess);
		case final ArrayStoreExpression arrayStore -> visit(arrayStore);
		case final BinaryExpression binary -> visit(binary);
		case final BitvecLiteral bitvec -> visit(bitvec);
		case final BitVectorAccessExpression bitvecAccess -> visit(bitvecAccess);
		case final BooleanLiteral booleanLit -> visit(booleanLit);
		case final FunctionApplication funApp -> visit(funApp);
		case final IdentifierExpression idExpr -> visit(idExpr);
		case final IfThenElseExpression ite -> visit(ite);
		case final IntegerLiteral intLit -> visit(intLit);
		case final QuantifierExpression quantified -> visit(quantified);
		case final RealLiteral realLit -> visit(realLit);
		case final StringLiteral stringLit -> visit(stringLit);
		case final StructAccessExpression structAccess -> visit(structAccess);
		case final StructConstructor structConstructor -> visit(structConstructor);
		case final UnaryExpression unary -> visit(unary);
		case final WildcardExpression wildcard -> visit(wildcard);
		}
		return expr;
	}

	protected void visit(final WildcardExpression expr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final UnaryExpression expr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final StructConstructor expr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final StructAccessExpression expr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final StringLiteral expr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final RealLiteral expr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final QuantifierExpression expr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final IntegerLiteral expr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final IfThenElseExpression expr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final IdentifierExpression expr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final FunctionApplication expr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final BooleanLiteral expr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final BitVectorAccessExpression expr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final BitvecLiteral expr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final BinaryExpression expr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final ArrayStoreExpression expr) {
		// empty because it may be overridden (but does not have to)
	}

	protected void visit(final ArrayAccessExpression expr) {
		// empty because it may be overridden (but does not have to)
	}
}