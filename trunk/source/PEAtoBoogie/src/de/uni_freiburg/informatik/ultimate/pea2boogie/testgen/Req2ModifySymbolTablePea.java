package de.uni_freiburg.informatik.ultimate.pea2boogie.testgen;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogiePrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DefaultLocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.BoogieDeclarations;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.Decision;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision;
import de.uni_freiburg.informatik.ultimate.lib.srparse.Durations;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.DeclarationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.DeclarationPattern.VariableCategory;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType.ReqPeas;
import de.uni_freiburg.informatik.ultimate.pea2boogie.Activator;
import de.uni_freiburg.informatik.ultimate.pea2boogie.IReqSymbolTable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.preferences.Pea2BoogiePreferences;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2Pea;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.IReq2PeaAnnotator;
import de.uni_freiburg.informatik.ultimate.pea2boogie.req2pea.ReqCheckAnnotator;
import de.uni_freiburg.informatik.ultimate.pea2boogie.staterecoverability.VerificationExpression;
import de.uni_freiburg.informatik.ultimate.pea2boogie.staterecoverability.VerificationExpressionContainer;
import de.uni_freiburg.informatik.ultimate.pea2boogie.staterecoverability.AuxStatement;
import de.uni_freiburg.informatik.ultimate.pea2boogie.staterecoverability.PeaPhaseProgramCounter;
import de.uni_freiburg.informatik.ultimate.pea2boogie.staterecoverability.StateRecoverabilityAuxStatement;
import de.uni_freiburg.informatik.ultimate.pea2boogie.staterecoverability.StateRecoverabilityGenerator;
import de.uni_freiburg.informatik.ultimate.pea2boogie.translator.ReqSymboltableBuilder;
import de.uni_freiburg.informatik.ultimate.pea2boogie.translator.ReqSymboltableBuilder.ErrorInfo;
import de.uni_freiburg.informatik.ultimate.pea2boogie.translator.ReqSymboltableBuilder.ErrorType;

public class Req2ModifySymbolTablePea implements IReq2Pea {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final List<DeclarationPattern> mInitPattern;
	private final List<ReqPeas> mReqPeas;
	private IReqSymbolTable mSymbolTable;
	private final Durations mDurations;
	private boolean mHasErrors;
	private final IPreferenceProvider prefs;
	private ILocation loc;
	private StateRecoverabilityGenerator stRecGen;
	
	public Req2ModifySymbolTablePea(final IUltimateServiceProvider services, final ILogger logger, final List<DeclarationPattern> init) {
		mServices = services;
		mLogger = logger;
		mInitPattern = init;
		mReqPeas = new ArrayList<>();
		mDurations = new Durations();
		prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
	}
	
	@Override
	public List<ReqPeas> getReqPeas() {
		return mReqPeas;
	}

	@Override
	public IReqSymbolTable getSymboltable() {
		return mSymbolTable;
	}

	@Override
	public Durations getDurations() {
		return mDurations;
	}

	@Override
	public void transform(IReq2Pea req2pea) {
		final VerificationExpressionContainer vec = getVerificationExpression(req2pea);
		
		final List<ReqPeas> simplePeas = req2pea.getReqPeas();
		final IReqSymbolTable oldSymbolTable = req2pea.getSymboltable();
		stRecGen = new StateRecoverabilityGenerator(mLogger, mServices, oldSymbolTable);
		final ReqSymboltableBuilder builder = new ReqSymboltableBuilder(mLogger, oldSymbolTable);
		
		//Passing the variable definitions
		for (final DeclarationPattern p : mInitPattern) {
			builder.addInitPattern(p);
			mDurations.addInitPattern(p);
		}
		
		//Übergabe der PEAs
		for (final ReqPeas reqpea : simplePeas) {
			mReqPeas.add(reqpea);
			final PatternType<?> pattern = reqpea.getPattern();
			mDurations.addNonInitPattern(pattern);
			for (final Entry<CounterTrace, PhaseEventAutomata> pea : reqpea.getCounterTrace2Pea()) {
				builder.addPea(reqpea.getPattern(), pea.getValue());
			}
		}
		
		//Collecting the PEAs and ProgramCounter
		//Necessary in Transformer since otherwise unused global variables would be in the Boogie code
		Map<VerificationExpression, Set<PeaPhaseProgramCounter>> veLocationMap = stRecGen.getRelevantLocationsFromPea(simplePeas, vec);
		
		List<AuxStatement> sreList = createGlobalVariableForVerificationExpression(builder, veLocationMap, vec);
		
		//Creating the statements
		createAssignBoolToGlobalVariableBeforeWhileLoop(sreList);
		createIfStatementInWhileLoop(sreList);
		
		mSymbolTable = builder.constructSymbolTable();
	}
	
	private void createIfStatementInWhileLoop(List<AuxStatement> auxStatements) {
		for(AuxStatement auxStatement : auxStatements) {
			if(auxStatement instanceof StateRecoverabilityAuxStatement) {
				StateRecoverabilityAuxStatement auxStatementStRec = (StateRecoverabilityAuxStatement) auxStatement;
				VerificationExpression ve = auxStatementStRec.getVerificationExpression();
				ILocation loc = auxStatementStRec.getBoogieLocation();
				// Create expression
				//Opposite of verification Expression
				Expression condition1 = stRecGen.createOppositeCondition(loc, BoogiePrimitiveType.toPrimitiveType(ve.getDataType()), ve.getVariable(), ve.getOperator(), ve.getValue());
				// Program counter state
				Expression condition2 = stRecGen.createExpression(loc, BoogieType.TYPE_INT, auxStatementStRec.getPcVariable(), Operator.COMPEQ, String.valueOf(auxStatementStRec.getPc()));
				Expression condition1And2 = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND, condition1, condition2);
				BooleanLiteral booleanLiteral = ExpressionFactory.createBooleanLiteral(loc, true);
				// Create assignment
				AssignmentStatement assignmentStatement = genAssignmentStmt(loc, auxStatementStRec.getRelatedVariable(), booleanLiteral);
				IfStatement ifStatement = new IfStatement(loc, condition1And2, new Statement[] {assignmentStatement}, new Statement[0]);				
				auxStatementStRec.setIfSt(ifStatement);
			}
		}
	}

	private VerificationExpressionContainer getVerificationExpression(IReq2Pea req2pea) {
		final VerificationExpressionContainer vec = new VerificationExpressionContainer(req2pea);
		//Gets verification expression from GUI
		String verExpr = prefs.getString(Pea2BoogiePreferences.LABEL_STATE_RECOVERABILITY_VER_EXPR);
		vec.addExpression(verExpr);
		return vec;
	}
	
	private List<AuxStatement> createGlobalVariableForVerificationExpression(ReqSymboltableBuilder builder, Map<VerificationExpression, Set<PeaPhaseProgramCounter>> veLocationMaptionMap, VerificationExpressionContainer vec) {
		List<AuxStatement> sreList = new ArrayList<>();
		for(Map.Entry<VerificationExpression, Set<PeaPhaseProgramCounter>> entry : veLocationMaptionMap.entrySet()) {
			for(PeaPhaseProgramCounter peaPhasePc : entry.getValue()) {
				String pcName = getPcName(peaPhasePc.getPea().getName());
				int pc = peaPhasePc.getPc();
					//Erstelle für jede angegebene Bedingung eine globale Variable für alle PCs
					String variable = entry.getKey().getVariable();
					String dataType = entry.getKey().getDataType();
					String globalVariable = pcName + pc + "_StRec_" + variable;
					StateRecoverabilityAuxStatement auxStatement = new StateRecoverabilityAuxStatement(peaPhasePc, globalVariable, pcName, pc, entry.getKey());
					sreList.add(builder.addAuxVar(auxStatement, globalVariable, "bool", null));
				}
				
			}
		return sreList;
	}
	
	private void createAssignBoolToGlobalVariableBeforeWhileLoop(List<AuxStatement> auxStatements) {
		for(AuxStatement auxStatement : auxStatements) {
			if(auxStatement instanceof StateRecoverabilityAuxStatement) {
				StateRecoverabilityAuxStatement auxStatementStateRecoverability = (StateRecoverabilityAuxStatement) auxStatement;
				BooleanLiteral booleanLiteral = ExpressionFactory.createBooleanLiteral(null, false);
				AssignmentStatement assignmentStatement = genAssignmentStmt(constructNewLocation(), auxStatementStateRecoverability.getRelatedVariable(), booleanLiteral);				
				auxStatementStateRecoverability.setAssignVar(assignmentStatement);
			}
		}
	}
	
	private String getPcName(String s) {
		//Decision<?> decision = phase.getClockInvariant().getDecision();
		//if(decision != null) {
		//	return decision.getVar();
		//}
		return s + "_pc";
	}
	
	private Matcher match(String text, String pattern) {
        Pattern p = Pattern.compile(pattern);
        Matcher m = p.matcher(text);
        return m;
    }
	
	private static AssignmentStatement genAssignmentStmt(final ILocation bl, final String id, final Expression val) {
		return genAssignmentStmt(bl, new VariableLHS(bl, id), val);
	}

	private static AssignmentStatement genAssignmentStmt(final ILocation bl, final VariableLHS lhs,
			final Expression val) {
		assert lhs.getLocation() == bl;
		return new AssignmentStatement(bl, new LeftHandSide[] { lhs }, new Expression[] { val });
	}
	
	private ILocation constructNewLocation() {
		return new DefaultLocation();
	}
	
	private IBoogieType getBoogieType(String type) {
		switch (type.toLowerCase()) {
		case "bool":
		case "real":
		case "int":
			return BoogiePrimitiveType.toPrimitiveType(type);
		case "event":
			return BoogieType.TYPE_BOOL;
		default:
			return BoogieType.TYPE_ERROR;
		}
	}

	@Override
	public boolean hasErrors() {
		return mHasErrors;
	}

	@Override
	public IReq2PeaAnnotator getAnnotator() {
		return new ReqCheckAnnotator(mServices, mLogger, getReqPeas(), getSymboltable(), getDurations());
	}

}
