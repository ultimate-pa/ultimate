package de.uni_freiburg.informatik.ultimate.reqtotest.graphtransformer;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Term2Expression;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TypeSortTranslator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.ReqGuardGraph;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.ReqSymbolTable;
import de.uni_freiburg.informatik.ultimate.reqtotest.req.TimedLabel;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class GraphToBoogie {
	
	private static final Attribute[] EMPTY_ATTRIBUTES = new Attribute[0];
	public static final String GLOBAL_CLOCK_VAR = "reqtotest_delta";
	public static final String LOCATION_PREFIX = "reqtotest_pc_";
	public static final String LOCATION_PRIME = "'";
	public static final String TEST_ORACLE_MARKER = "TEST_ORACLE_MARKER";
		
	private final ILogger mLogger;
	private final ReqSymbolTable mSymbolTable;
	
	private final BoogieLocation mDummyLocation;
	private final List<ReqGuardGraph> mRequirements;
	private final Unit mUnit;
	
	private final Map<ReqGuardGraph, String> mGraphToPc;
	private final Map<ReqGuardGraph, String> mGraphToPcPrime;
	
	private final Term2Expression mTerm2Expression;
	private final Script mScript;
	private final ManagedScript mManagedScript;
	private final AuxVarGen mThreeValuedAuxVarGen;
	
	public GraphToBoogie(final ILogger logger, final IUltimateServiceProvider services,
			final IToolchainStorage storage,  ReqSymbolTable symbolTable, AuxVarGen threeValuedAuxVarGen,
			List<ReqGuardGraph> requirements, Script scipt, ManagedScript managedScipt) {
		mLogger = logger;
		mSymbolTable = symbolTable;
		mDummyLocation = generateDummyLocation();
		mRequirements = requirements;
		
		mGraphToPc = new LinkedHashMap<>();
		mGraphToPcPrime = new LinkedHashMap<>();
		
		generatePcVars();

		mScript = scipt;
		mManagedScript = managedScipt;
		mThreeValuedAuxVarGen = threeValuedAuxVarGen;
		
		final HashRelation<Sort, IBoogieType> sortToType = new HashRelation<>();
		sortToType.addPair(mManagedScript.getScript().sort("Int"), BoogieType.TYPE_INT);
		sortToType.addPair(mManagedScript.getScript().sort("Real"), BoogieType.TYPE_REAL);
		sortToType.addPair(mManagedScript.getScript().sort("Bool"), BoogieType.TYPE_BOOL);
		mTerm2Expression = new Term2Expression(new TypeSortTranslator(sortToType, mScript,
				services), symbolTable, mManagedScript);
		
		final List<Declaration> decls = new ArrayList<>();
		decls.addAll(mSymbolTable.constructVariableDeclarations());
		decls.addAll(generateEncodingVarDeclaration());
		decls.add(getMainProcedure());
		mUnit = new Unit(mDummyLocation, decls.toArray(new Declaration[decls.size()]));
		
		
	}
	
	private void generatePcVars() {
		int i = 0;
		for(ReqGuardGraph req: mRequirements) {
			mGraphToPc.put(req, GraphToBoogie.LOCATION_PREFIX + Integer.toString(i));
			mGraphToPcPrime.put(req, GraphToBoogie.LOCATION_PREFIX + Integer.toString(i) + LOCATION_PRIME);
			i++;
		}
	}
	
	public Unit getAst() {
		return mUnit;
	}
	
	private Declaration getMainProcedure() {
		
		final ModifiesSpecification mod = new ModifiesSpecification(mDummyLocation, false, generateModifiesVariableList());
		final ModifiesSpecification[] modArray = new ModifiesSpecification[1];
		modArray[0] = mod;
		
		final Attribute[] attribute = new Attribute[0];
		final String[] typeParams = new String[0];
		final VarList[] inParams = new VarList[0];
		final VarList[] outParams = new VarList[0];
		
		final VariableDeclaration[] localVars = new VariableDeclaration[0];
		final Body body = new Body(mDummyLocation, localVars, generateProcedureBody());
		
		
		return new Procedure(mDummyLocation, attribute, "testGen", typeParams, inParams, outParams, modArray, body);
	}
	
	private Statement[] generateProcedureBody() {
		final List<Statement> statements = new ArrayList<>();
		statements.addAll(mSymbolTable.constructConstantAssignments());
		statements.addAll(generatePcInitialization());
		statements.addAll(generateClockInitialization());
		statements.add(generateWhileStatement());
		return statements.toArray(new Statement[statements.size()]);
	}
	
	private Statement generateWhileStatement() {
		return new WhileStatement(mDummyLocation,  new WildcardExpression(mDummyLocation), 
				new LoopInvariantSpecification[0], generateWhileBody());
	}
	
	private Statement[] generateWhileBody() {
		final List<Statement> statements = new ArrayList<>();
		statements.add(new HavocStatement(new BoogieLocation("", 0, 0, 1, 1), generateHavocVariableList()));
		for(ReqGuardGraph graph: mRequirements) {
			statements.addAll(graphToBoogie(graph));
		}
		statements.addAll(generateDefineUseAssumtions());
		statements.addAll(generateTestOracleAssertion());
		statements.addAll(generateNextLoopStateAssignment());
		statements.addAll(generateClockUpdates());
		return statements.toArray(new Statement[statements.size()]);
	}
	
	private List<Statement> graphToBoogie(ReqGuardGraph reqId) {

		final HashSet<ReqGuardGraph> visited = new HashSet<>();
		final Queue<ReqGuardGraph> queue = new LinkedList<>();
		queue.add(reqId);
		Statement[] elsePart = new Statement[0];
		while(queue.size() > 0) {
			ReqGuardGraph sourceLocation = queue.poll();
			visited.add(sourceLocation);
			Statement[] innerIf = new Statement[] {new AssumeStatement(mDummyLocation, new BooleanLiteral(mDummyLocation, false))};
			for(int i = 0; i < sourceLocation.getOutgoingNodes().size();  i++) {
				ReqGuardGraph successorLocation = sourceLocation.getOutgoingNodes().get(i);
				TimedLabel label = sourceLocation.getOutgoingEdgeLabels().get(i);
			
				if(!visited.contains(successorLocation) && !queue.contains(successorLocation)) {
					queue.add(successorLocation);
				}
				//generate the inner if (... "then transition to __successorLocation__ if __label__ holds ")
				innerIf = generateInnerIf(innerIf, reqId, sourceLocation, successorLocation, label);
			}
			//generate the outer if ("if in location __sourceLocation__ ...")
			elsePart = new Statement[] {(generateOuterIf(reqId, sourceLocation, innerIf, elsePart))};
		}
		//TODO this is ugly
		final List<Statement> statements = new ArrayList<>();
		statements.add(elsePart[0]);
		return statements;
	}
	
	private Statement generateOuterIf(ReqGuardGraph req, ReqGuardGraph pivoth, Statement[] body, Statement[] elsePart) {
		final Expression lhs = new IntegerLiteral(mDummyLocation, Integer.toString(pivoth.getLabel()));
		final Expression rhs = new IdentifierExpression(mDummyLocation, mGraphToPc.get(req));
		final BinaryExpression condition = new BinaryExpression(mDummyLocation, BinaryExpression.Operator.COMPEQ, lhs, rhs);
		return new IfStatement(mDummyLocation, condition, body, elsePart);
	} 
	
	private Statement[] generateInnerIf(Statement[] innerIf, ReqGuardGraph reqId, ReqGuardGraph source, ReqGuardGraph successor, TimedLabel label) {
		Statement[] body;
		Statement setPcNextState = generateVarIntAssignment(mGraphToPcPrime.get(reqId), successor.getLabel());
		Statement guardAssume = new AssumeStatement(mDummyLocation, mTerm2Expression.translate(label.getGuard()));
		ReqGraphAnnotation annotation = new ReqGraphAnnotation(reqId, label, source);
		annotation.annotate(guardAssume);
		if (label.getReset() != null) {
			Statement resetClock = generateVarIntAssignment(label.getReset().getName(), 0);
			body = new Statement[] {guardAssume, resetClock, setPcNextState};
		} else {
			body = new Statement[] {guardAssume, setPcNextState};
		}
		IfStatement ifStatement = new IfStatement(mDummyLocation, new WildcardExpression(mDummyLocation), body, innerIf);
		return new Statement[] {ifStatement};
	}
	
	private List<Declaration> generateEncodingVarDeclaration() {
		final List<Declaration> statements = new ArrayList<>();
		Collection<String> values = mGraphToPc.values();
		String[] idents = values.toArray(new String[values.size()]);
		VarList[] varList = new VarList[] { new VarList(mDummyLocation, idents,  BoogieType.TYPE_INT.toASTType(mDummyLocation)) };
		statements.add(new VariableDeclaration(mDummyLocation, EMPTY_ATTRIBUTES, varList));
		Collection<String> valuesPrimed = mGraphToPcPrime.values();
		String[] identsPrimed = valuesPrimed.toArray(new String[valuesPrimed.size()]);
		VarList[] varListPrimed = new VarList[] { new VarList(mDummyLocation, identsPrimed,  BoogieType.TYPE_INT.toASTType(mDummyLocation)) };
		statements.add(new VariableDeclaration(mDummyLocation, EMPTY_ATTRIBUTES, varListPrimed));
		//add encoding variable "delta"
		varList = new VarList[] { new VarList(mDummyLocation, new String[] {GLOBAL_CLOCK_VAR},  BoogieType.TYPE_INT.toASTType(mDummyLocation)) };
		statements.add(new VariableDeclaration(mDummyLocation, EMPTY_ATTRIBUTES, varList));
		return statements;
	}
	
	private List<Statement> generateNextLoopStateAssignment(){
		final List<Statement> statements = new ArrayList<>();
		for(ReqGuardGraph req: mRequirements) {
			statements.add(generateVarVarAssignment(mGraphToPc.get(req), mGraphToPcPrime.get(req)));
		}
		return statements;
	}
	
	private Statement generateVarVarAssignment(String asignee, String asignment) {
		final LeftHandSide[] lhs = new LeftHandSide[] {new VariableLHS(mDummyLocation, asignee)};
		final Expression[] rhs = new Expression[] {new IdentifierExpression(mDummyLocation, asignment)};
		return new AssignmentStatement(mDummyLocation,lhs,rhs );
	}
	
	private Statement generateVarIntAssignment(String asignee, int value) {
		final LeftHandSide[] lhs = new LeftHandSide[] {new VariableLHS(mDummyLocation, asignee)};
		final Expression[] rhs = new Expression[] {new IntegerLiteral(mDummyLocation, Integer.toString(value))};
		return new AssignmentStatement(mDummyLocation,lhs,rhs );
	}
	
	private VariableLHS[] generateHavocVariableList(){
		final List<String> modifiedVarsList = new ArrayList<>();

		modifiedVarsList.addAll(mSymbolTable.getInputVars());
		modifiedVarsList.addAll(mSymbolTable.getHiddenVars());
		modifiedVarsList.addAll(mSymbolTable.getOutputVars());
		modifiedVarsList.addAll(mSymbolTable.getAuxVars());
		//modifiedVarsList.addAll(mGraphToPrimePc.values());
		
		final VariableLHS[] modifiedVars = new VariableLHS[modifiedVarsList.size()];
		for (int i = 0; i < modifiedVars.length; i++) {
			modifiedVars[i] = new VariableLHS(mDummyLocation, modifiedVarsList.get(i));
		}
		return modifiedVars;
	}
	
	private VariableLHS[] generateModifiesVariableList(){
		final List<String> modifiedVarsList = new ArrayList<>();

		modifiedVarsList.addAll(mSymbolTable.getInputVars());
		modifiedVarsList.addAll(mSymbolTable.getHiddenVars());
		modifiedVarsList.addAll(mSymbolTable.getOutputVars());
		modifiedVarsList.addAll(mSymbolTable.getConstVars());
		modifiedVarsList.addAll(mSymbolTable.getAuxVars());
		modifiedVarsList.addAll(mSymbolTable.getClockVars());
		modifiedVarsList.addAll(mGraphToPcPrime.values());
		modifiedVarsList.addAll(mGraphToPc.values());
		modifiedVarsList.add(GraphToBoogie.GLOBAL_CLOCK_VAR);
		
		final VariableLHS[] modifiedVars = new VariableLHS[modifiedVarsList.size()];
		for (int i = 0; i < modifiedVars.length; i++) {
			modifiedVars[i] = new VariableLHS(mDummyLocation, modifiedVarsList.get(i));
		}
		return modifiedVars;
	}
	
	private List<Statement> generatePcInitialization() {
		final List<Statement> statements = new ArrayList<>();
		for(ReqGuardGraph req: mRequirements) {
			statements.add(generateVarIntAssignment(mGraphToPc.get(req), req.getLabel()));
		}
		return statements;
	}
	
	private List<Statement> generateClockInitialization() {
		final List<Statement> statements = new ArrayList<>();
		for(String clock: mSymbolTable.getClockVars()) {
			statements.add(generateVarIntAssignment(clock, 0));
		}
		statements.add(generateVarIntAssignment(GraphToBoogie.GLOBAL_CLOCK_VAR, 0));
		return statements;
	}
	
	
	private static BoogieLocation generateDummyLocation() {
		return new BoogieLocation("", 1, 1, 1, 1);
	}
	
	private List<Statement> generateDefineUseAssumtions(){
		final List<Statement> defineUseAssumtptions = new ArrayList<>();
		final List<Term> guards = mThreeValuedAuxVarGen.getDefineAssumeGuards();
		for(Term guard: guards) {
			Statement assume = new AssumeStatement(mDummyLocation, mTerm2Expression.translate(guard));
			defineUseAssumtptions.add(assume);
		}
		return defineUseAssumtptions;
	}
	
	private List<Statement> generateTestOracleAssertion(){
		final List<Statement> oracles = new ArrayList<>();	
				
		// dummy assertion to mark the program location
		NamedAttribute attribute = new NamedAttribute(mDummyLocation, TEST_ORACLE_MARKER , new Expression[0] );
		Statement assertion = new AssertStatement(mDummyLocation, new NamedAttribute[] {attribute}, new BooleanLiteral(mDummyLocation, true));	
		oracles.add(assertion);
		
		final Map<ReqGuardGraph, Term> guards = mThreeValuedAuxVarGen.getOracleAssertions();
		for(ReqGuardGraph reqId: guards.keySet()) {
			Term guard = guards.get(reqId);
			oracles.add(generateTestOracleAssertion(reqId, guard));
		}
		return oracles;
	}
	
	private Statement generateTestOracleAssertion(ReqGuardGraph reqId, Term guard) {
		AssertStatement assertion = new AssertStatement(mDummyLocation, mTerm2Expression.translate(guard));
		ReqGraphOracleAnnotation annotation = 
				new ReqGraphOracleAnnotation(reqId, guard, mThreeValuedAuxVarGen.getEffectVariables(reqId));
		annotation.annotate(assertion);
		return assertion;
	}
	
	private List<Statement> generateClockUpdates(){
		List<Statement> stmts = new ArrayList<>();
		stmts.add(new HavocStatement(mDummyLocation, 
				new VariableLHS[] {new VariableLHS(mDummyLocation, GraphToBoogie.GLOBAL_CLOCK_VAR)} ));
		stmts.add(new AssumeStatement(mDummyLocation,
				new BinaryExpression(mDummyLocation, BinaryExpression.Operator.COMPGEQ,
						new IdentifierExpression(mDummyLocation, GraphToBoogie.GLOBAL_CLOCK_VAR), new IntegerLiteral(mDummyLocation, "1"))
				));
		for(String clockVar: mSymbolTable.getClockVars()) {
			stmts.add(new AssignmentStatement(mDummyLocation, new VariableLHS[] {new VariableLHS(mDummyLocation, clockVar)},
					new Expression[] {new BinaryExpression(mDummyLocation, BinaryExpression.Operator.ARITHPLUS,
							new IdentifierExpression(mDummyLocation, clockVar),
							new IdentifierExpression(mDummyLocation, GraphToBoogie.GLOBAL_CLOCK_VAR)
					)}));
			}
		return stmts;
	}

}




























