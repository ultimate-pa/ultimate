package de.uni_freiburg.informatik.ultimate.reqtotest;

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
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogiePrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InitializationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InitializationPattern.VariableCategory;
import de.uni_freiburg.informatik.ultimate.pea2boogie.IReqSymbolExpressionTable;

public class ReqSymbolExpressionTable implements IReqSymbolExpressionTable{
	
	private static final Attribute[] EMPTY_ATTRIBUTES = new Attribute[0];

	private final Map<String, BoogieType> mId2Type;
	private final Map<String, IdentifierExpression> mId2IdExpr;
	private final Map<String, VariableLHS> mId2VarLHS;

	private final Map<PatternType, BoogieLocation> mReq2Loc;
	
	private final ILogger mLogger;
	
	private final Set<String> mStateVars;
	private final Set<String> mConstVars;
	
	public ReqSymbolExpressionTable(final ILogger logger) {
		mId2Type = new LinkedHashMap<>();
		mId2IdExpr = new LinkedHashMap<>();
		mId2VarLHS = new LinkedHashMap<>();
		mReq2Loc = new LinkedHashMap<>();

		mLogger = logger;
		
		mStateVars = new LinkedHashSet<>();
		mConstVars = new LinkedHashSet<>();

		// extract pcid vars, clock vars, state vars, primed state vars, and event vars
		//extractVariablesFromAutomata(req2Automata);
	}
	
	public List<Declaration> constructVariableDeclarations() {
		final List<Declaration> decls = new ArrayList<>();

		decls.addAll(constructVariableDeclarations(mConstVars));
		decls.addAll(constructVariableDeclarations(mStateVars));

		return decls;
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

	public void extractVariablesFromInit(final InitializationPattern init) {
		final BoogiePrimitiveType type = toPrimitiveType(init.getType());
		final String name = init.getId();
		if (type == BoogieType.TYPE_ERROR) {
			//addTypeError(name, new TypeErrorInfo(TypeErrorType.NONE_TYPE, init));
			return;
		}

		if (init.getCategory() != VariableCategory.CONST) {
			addVar(name, type, init, mStateVars);
		} else {
			addVar(name, type, init, mConstVars);
		}
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
	
	private void addVar(final String name, final BoogieType type, final PatternType source, final Set<String> kind) {
		if (type == null && (!kind.contains(name) || !mId2Type.containsKey(name))) {
			throw new AssertionError();
		}

		if (kind != null) {
			kind.add(name);
		}

		final BoogieType old = mId2Type.put(name, type);
		if (old != null && old != type) {
			//addTypeError(name, new TypeErrorInfo(TypeErrorType.DUPLICATE_DECLARATION, source));
			mId2Type.put(name, BoogieType.TYPE_ERROR);
			return;
		}

		final ILocation loc = getLocation(source);
		final IdentifierExpression idExpr = ExpressionFactory.constructIdentifierExpression(loc, type, name,
				DeclarationInformation.DECLARATIONINFO_GLOBAL);
		mId2IdExpr.put(name, idExpr);
		mId2VarLHS.put(name, new VariableLHS(loc, name));
	}
	
	private ILocation getLocation(final PatternType source) {
		// TODO: Fix locations
		final ILocation loc = mReq2Loc.get(source);
		if (loc != null) {
			return loc;
		}
		final BoogieLocation newLoc = new BoogieLocation("", -1, -1, -1, -1);
		mReq2Loc.put(source, newLoc);
		return newLoc;
	}

	@Override
	public IdentifierExpression getIdentifierExpression(String name) {
		return mId2IdExpr.get(name);
	}

}
