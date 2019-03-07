package de.uni_freiburg.informatik.ultimate.reqtotest.req;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogiePrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InitializationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InitializationPattern.VariableCategory;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ITerm2ExpressionSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.pea2boogie.IReqSymbolExpressionTable;
import de.uni_freiburg.informatik.ultimate.reqtotest.graphtransformer.FakeBoogieVar;

public class ReqSymbolTable implements IReqSymbolExpressionTable, ITerm2ExpressionSymbolTable{
	
	private static final Attribute[] EMPTY_ATTRIBUTES = new Attribute[0];

	private final Map<String, BoogieType> mId2Type;
	private final Map<String, IdentifierExpression> mId2IdExpr;
	private final Map<String, Expression> mConst2Val;
	
	private final ILogger mLogger;
	
	private final Set<String> mStateVars;
	private final Set<String> mConstVars;
	
	private final Set<String> mInputVars;
	private final Set<String> mHiddenVars;
	private final Set<String> mOutputVars;
	private final Set<String> mAuxVars;
	private final Set<String> mClockVars;
	
	private final ILocation mDummyLocation;
	
	public ReqSymbolTable(final ILogger logger) {
		mId2Type = new LinkedHashMap<>();
		mId2IdExpr = new LinkedHashMap<>();
		mConst2Val = new LinkedHashMap<>();

		mLogger = logger;
		
		mStateVars = new LinkedHashSet<>();
		mConstVars = new LinkedHashSet<>();
		
		mInputVars = new LinkedHashSet<>();
		mHiddenVars = new LinkedHashSet<>();
		mOutputVars = new LinkedHashSet<>();
		mAuxVars = new LinkedHashSet<>();
		mClockVars = new LinkedHashSet<>();

		mDummyLocation = new BoogieLocation("", -1, -1, -1, -1);
	}
	
	public List<Declaration> constructVariableDeclarations() {
		final List<Declaration> decls = new ArrayList<>();

		decls.addAll(constructVariableDeclarations(mConstVars));
		decls.addAll(constructVariableDeclarations(mStateVars));
		decls.addAll(constructVariableDeclarations(mAuxVars));
		decls.addAll(constructVariableDeclarations(mClockVars));

		return decls;
	}
	
	public boolean isConstVar(String e) {
		return mConstVars.contains(e);
	}
	
	public boolean isInput(String e) {
		return mInputVars.contains(e);
	}
	
	public boolean isObservable(String e) {
		return isInput(e) || isOutput(e);
	}
	
	public boolean isAuxVar(String v) {
		return mAuxVars.contains(v);
	}
	
	public Set<String> getHiddenVars(){
		return mHiddenVars;
	}
	
	public Set<String> getOutputVars(){
		return mOutputVars;
	}
	
	public Set<String> getInputVars(){
		return mInputVars;
	}
	
	public Set<String> getConstVars(){
		return mConstVars;
	}
	
	public Set<String> getAuxVars(){
		return mAuxVars;
	}
	
	public Set<String> getClockVars(){
		return mClockVars;
	}
	
	public boolean isOutput(String ident) {
		return mOutputVars.contains(ident);
	}
	
	public void updateVariableCategoryInput(String name) {
		mInputVars.add(name);
		mOutputVars.remove(name);
		mHiddenVars.remove(name);
	}
	
	public void updateVariableCategoryOutput(String name) {
		mInputVars.remove(name);
		mOutputVars.add(name);
		mHiddenVars.remove(name);
	}
	
	public void updateVariableCategoryHidden(String name) {
		mInputVars.remove(name);
		mOutputVars.remove(name);
		mHiddenVars.add(name);
	}
	
	public void extractVariablesFromInit(final InitializationPattern init) {
		final BoogiePrimitiveType type = toPrimitiveType(init.getType());
		final String name = init.getId();
		if (type == BoogieType.TYPE_ERROR) {
			throw new RuntimeException("Variable has not Type: " + init.toString());
		}

		if (init.getCategory() == VariableCategory.CONST) {
			addVar(name, type, init, mConstVars);
			mConst2Val.put(name, init.getExpression());
		} else if (init.getCategory() == VariableCategory.IN){
			addVar(name, type, init, mStateVars);
			mInputVars.add(name);
		} else if (init.getCategory() == VariableCategory.OUT){
			addVar(name, type, init, mStateVars);
			mOutputVars.add(name);
		} else if (init.getCategory() == VariableCategory.HIDDEN){
			addVar(name, type, init, mStateVars);
			mHiddenVars.add(name);
		} 
	}
	
	public List<Statement> constructConstantAssignments() {
		final List<Statement> assignments = new ArrayList<>();
		for(String name: mConstVars) {
			assignments.add(new AssignmentStatement(mDummyLocation, 
					new VariableLHS[] {new VariableLHS(mDummyLocation, name)}, new Expression[] {mConst2Val.get(name)}));
		}
		return assignments;
		
	}
	
	private List<Declaration> constructVariableDeclarations(final Collection<String> identifiers) {
		final List<? extends VarList> varlist = constructVarLists(identifiers);
		return varlist.stream()
				.map(a -> new VariableDeclaration(a.getLocation(), EMPTY_ATTRIBUTES, new VarList[] { a }))
				.collect(Collectors.toList());
	}
	

	private List<? extends VarList> constructVarLists(final Collection<String> identifiers) {
		if (identifiers.isEmpty()) {
			return Collections.emptyList();
		}
		return identifiers.stream().map(this::constructVarlist).filter(a -> a != null).collect(Collectors.toList());
	}
	
	private VarList constructVarlist(final String identifier) {
		final BoogieType type = mId2Type.get(identifier);
		final IdentifierExpression idExpr = mId2IdExpr.get(identifier);
		if (type == null || idExpr == null) {
			return null;
		}
		return new VarList(idExpr.getLocation(), new String[] { identifier }, type.toASTType(idExpr.getLocation()));
	}
	
	
	private static BoogiePrimitiveType toPrimitiveType(final String type) {
		switch (type.toLowerCase()) {
		case "bool":
			return BoogieType.TYPE_BOOL;
		case "real":
			return BoogieType.TYPE_REAL;
		case "int":
			return BoogieType.TYPE_INT;
		default:
			return BoogieType.TYPE_ERROR;
		}
	}
	
	public void addAuxVar(final String name, final BoogieType type) {
		mAuxVars.add(name);
		addVar(name,type);
	}
	
	public void addClockVar(final String name, final BoogieType type) {
		mClockVars.add(name);
		addVar(name,type);
	}
	
	private void addVar(final String name, final BoogieType type, final PatternType source, final Set<String> kind) {
		if (type == null && (!kind.contains(name) || !mId2Type.containsKey(name))) {
			throw new AssertionError();
		}
		if (kind != null) {
			kind.add(name);
		}
		addVar(name,type);
	}
	
	private void addVar(final String name, final BoogieType type) {
		final BoogieType old = mId2Type.put(name, type);
		if (old != null && old != type) {
			//addTypeError(name, new TypeErrorInfo(TypeErrorType.DUPLICATE_DECLARATION, source));
			mId2Type.put(name, BoogieType.TYPE_ERROR);
			return;
		}

		final IdentifierExpression idExpr = ExpressionFactory.constructIdentifierExpression(mDummyLocation, type, name,
				DeclarationInformation.DECLARATIONINFO_GLOBAL);
		mId2IdExpr.put(name, idExpr);
	}
	

	@Override
	public IdentifierExpression getIdentifierExpression(String name) {
		return mId2IdExpr.get(name);
	}

	@Override
	public BoogieConst getProgramConst(ApplicationTerm term) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IProgramVar getProgramVar(TermVariable term) {
		// According to interface specification null is always correct as every variable is a global one.
		return new FakeBoogieVar(mId2Type.get(term.getName()), term.getName()); 
	}

	@Override
	public Map<String, String> getSmtFunction2BoogieFunction() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public ILocation getLocation(IProgramVar pv) {
		return mDummyLocation;
	}

	@Override
	public DeclarationInformation getDeclarationInformation(IProgramVar pv) {
		// TODO Auto-generated method stub
		return null;
	}

}
