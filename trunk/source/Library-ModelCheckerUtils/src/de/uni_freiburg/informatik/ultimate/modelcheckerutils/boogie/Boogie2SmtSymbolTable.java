package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieNonOldVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieOldVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.model.boogie.LocalBoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;

/**
 * Stores a mapping from Boogie identifiers to BoogieVars and a mapping from
 * TermVariables that are representatives of BoogieVars to these BoogieVars.
 * @author Matthias Heizmann
 *
 */
public class Boogie2SmtSymbolTable {
	private final BoogieDeclarations m_BoogieDeclarations;
	private final Script m_Script; 
	private final TypeSortTranslator m_TypeSortTranslator;
	private final Map<String, BoogieNonOldVar> m_Globals = 
			new HashMap<String, BoogieNonOldVar>();
	private final Map<String, BoogieVar> m_OldGlobals = 
			new HashMap<String, BoogieVar>();
	private final Map<String, Map<String, BoogieVar>> m_SpecificationInParam = 
			new HashMap<String, Map<String, BoogieVar>>();
	private final Map<String, Map<String, BoogieVar>> m_SpecificationOutParam = 
			new HashMap<String, Map<String, BoogieVar>>();
	private final Map<String, Map<String, BoogieVar>> m_ImplementationInParam = 
			new HashMap<String, Map<String, BoogieVar>>();
	private final Map<String, Map<String, BoogieVar>> m_ImplementationOutParam = 
			new HashMap<String, Map<String, BoogieVar>>();
	private final Map<String, Map<String, BoogieVar>> m_ImplementationLocals = 
			new HashMap<String, Map<String, BoogieVar>>();
	private final Map<String, BoogieConst> m_Constants = 
			new HashMap<String, BoogieConst>();
	
	private final Map<TermVariable,BoogieVar> m_SmtVar2BoogieVar = 
			new HashMap<TermVariable,BoogieVar>();
	private final Map<BoogieVar,DeclarationInformation> m_BoogieVar2DeclarationInformation = 
			new HashMap<BoogieVar,DeclarationInformation>();
	private final Map<ApplicationTerm, BoogieConst> m_SmtConst2BoogieConst = 
			new HashMap<ApplicationTerm,BoogieConst>();
	
	final Map<String,String> m_BoogieFunction2SmtFunction = 
			new HashMap<String,String>();
	final Map<String,String> m_SmtFunction2BoogieFunction = 
			new HashMap<String,String>();
	
	
	public Boogie2SmtSymbolTable(BoogieDeclarations boogieDeclarations,
			Script script,
			TypeSortTranslator typeSortTranslator) {
		super();
		m_Script = script;
		m_TypeSortTranslator = typeSortTranslator;
		m_BoogieDeclarations = boogieDeclarations;
		
		for (ConstDeclaration decl : m_BoogieDeclarations.getConstDeclarations()) {
			declareConstants(decl);
		}
		
		for (FunctionDeclaration decl : m_BoogieDeclarations.getFunctionDeclarations()) {
			declareFunction(decl);
		}
		
		for (VariableDeclaration decl : m_BoogieDeclarations.getGlobalVarDeclarations()) {
			declareGlobalVariables(decl);
		}
		
		for (String procId : m_BoogieDeclarations.getProcSpecification().keySet()) {
			Procedure procSpec = m_BoogieDeclarations.getProcSpecification().get(procId);
			Procedure procImpl = m_BoogieDeclarations.getProcImplementation().get(procId);
			if (procImpl == null) {
				declareSpec(procSpec);
			} else {
				declareSpecImpl(procSpec, procImpl);
			}
		}
	}

	private void putNew(String procId, String varId, BoogieVar bv, Map<String, Map<String, BoogieVar>> map) {
		Map<String, BoogieVar> varId2BoogieVar = map.get(procId);
		if (varId2BoogieVar == null) {
			varId2BoogieVar = new HashMap<String, BoogieVar>();
			map.put(procId, varId2BoogieVar);
		}
		BoogieVar previousValue = varId2BoogieVar.put(varId, bv);
		assert previousValue == null : "variable already contained";
	}
	
	private <VALUE> void  putNew(String varId, VALUE value, Map<String, VALUE> map) {
		VALUE previousValue = map.put(varId, value);
		assert previousValue == null : "variable already contained";
	}
	
	private BoogieVar get(String varId, String procId, Map<String, Map<String, BoogieVar>> map) {
		Map<String, BoogieVar> varId2BoogieVar = map.get(procId);
		if (varId2BoogieVar == null) {
			return null;
		} else {
			return varId2BoogieVar.get(varId);
		}
	}
	
	public static boolean isSpecification(Procedure spec) {
		return spec.getSpecification() != null;
	}
	
	public static boolean isImplementation(Procedure impl) {
		return impl.getBody() != null;
	}
	
	public Script getScript() {
		return m_Script;
	}

	public BoogieVar getBoogieVar(String varId, DeclarationInformation declarationInformation, boolean inOldContext) {
		final BoogieVar result;
		StorageClass storageClass = declarationInformation.getStorageClass();
		String procedure = declarationInformation.getProcedure();
		switch (storageClass) {
		case GLOBAL:
			if (inOldContext) {
				result = m_OldGlobals.get(varId);
			} else {
				result = m_Globals.get(varId);
			}
			break;
		case PROC_FUNC_INPARAM:
//			result = get(varId, procedure, m_SpecificationInParam);
//			break;
		case IMPLEMENTATION_INPARAM:
			result = get(varId, procedure, m_ImplementationInParam);
			break;
		case PROC_FUNC_OUTPARAM:
//			result = get(varId, procedure, m_SpecificationOutParam);
//			break;
		case IMPLEMENTATION_OUTPARAM:
			result = get(varId, procedure, m_ImplementationOutParam);
			break;
		case LOCAL:
			result = get(varId, procedure, m_ImplementationLocals);
			break;
		case IMPLEMENTATION:
		case PROC_FUNC:
		case QUANTIFIED:
		default:
			throw new AssertionError("inappropriate decl info");
		}
		return result;
	}
	
	public BoogieVar getBoogieVar(TermVariable tv) {
		return m_SmtVar2BoogieVar.get(tv);
	}
	
	public DeclarationInformation getDeclarationInformation(BoogieVar bv) {
		return m_BoogieVar2DeclarationInformation.get(bv);
	}
	
	private void declareConstants(ConstDeclaration constdecl) {
		VarList varlist = constdecl.getVarList();
		Sort[] paramTypes = new Sort[0];
		IType iType = varlist.getType().getBoogieType();
		Sort sort = m_TypeSortTranslator.getSort(iType, varlist);
		for (String constId : varlist.getIdentifiers()) {
			m_Script.declareFun(constId, paramTypes, sort);
			ApplicationTerm constant = (ApplicationTerm) m_Script.term(constId);
			BoogieConst boogieConst = new BoogieConst(constId, iType, constant);
			BoogieConst previousValue = m_Constants.put(constId, boogieConst);
			assert previousValue == null : "constant already contained";
			m_SmtConst2BoogieConst.put(constant, boogieConst);
		}
	}
	
	public BoogieConst getBoogieConst(String constId) {
		return m_Constants.get(constId);
	}
	
	public BoogieConst getBoogieConst(ApplicationTerm smtConstant) {
		return m_SmtConst2BoogieConst.get(smtConstant);
	}
	
	private void declareFunction(FunctionDeclaration funcdecl) {
		// for (Attribute attr : funcdecl.getAttributes()) {
		// if (attr instanceof NamedAttribute) {
		// NamedAttribute nattr = (NamedAttribute) attr;
		// if (nattr.getName().equals("bvint")
		// && nattr.getValues().length == 1
		// && nattr.getValues()[0] instanceof StringLiteral
		// && ((StringLiteral)nattr.getValues()[0]).getValue().equals("ITE")) {
		// /* TODO: make sanity check of parameter types ?? */
		// itefunctions.add(funcdecl.getIdentifier());
		// return;
		// }
		// }
		// }
		String id = funcdecl.getIdentifier();
		// String smtID = "f_"+quoteId(id);
		String smtID = Boogie2SMT.quoteId(id);
		int numParams = 0;
		for (VarList vl : funcdecl.getInParams()) {
			int ids = vl.getIdentifiers().length;
			numParams += ids == 0 ? 1 : ids;
		}

		Sort[] paramSorts = new Sort[numParams];
		int paramNr = 0;
		for (VarList vl : funcdecl.getInParams()) {
			int ids = vl.getIdentifiers().length;
			if (ids == 0) {
				ids = 1;
			}
			IType paramType = vl.getType().getBoogieType();
			Sort paramSort = m_TypeSortTranslator.getSort(paramType, funcdecl);
			for (int i = 0; i < ids; i++) {
				paramSorts[paramNr++] = paramSort;
			}
		}
		IType resultType = funcdecl.getOutParam().getType().getBoogieType();
		Sort resultSort = m_TypeSortTranslator.getSort(resultType, funcdecl);
		m_Script.declareFun(smtID, paramSorts, resultSort);
		m_BoogieFunction2SmtFunction.put(id, smtID);
		m_SmtFunction2BoogieFunction.put(smtID, id);
	}
	
	public Map<String, String> getSmtFunction2BoogieFunction() {
		return m_SmtFunction2BoogieFunction;
	}
	
	
	private void declareGlobalVariables(VariableDeclaration vardecl) {
		for (VarList vl : vardecl.getVariables()) {
			for (String id : vl.getIdentifiers()) {
				IType type = vl.getType().getBoogieType();
				BoogieNonOldVar global = constructGlobalBoogieVar(
						id, type, vl);
				putNew(id, global, m_Globals);
				BoogieVar oldGlobal = global.getOldVar();
				putNew(id, oldGlobal, m_OldGlobals);
			}
		}
	}
	
	/**
	 * Return global variables;
	 */
	public Map<String, BoogieNonOldVar> getGlobals() {
		return Collections.unmodifiableMap(m_Globals);
	}
	
	private void declareSpecImpl(Procedure spec, Procedure impl) {
		assert (spec == impl || isSpecAndImpl(spec, impl));
		String procId = spec.getIdentifier();
		assert procId.equals(impl.getIdentifier());
		declareParams(procId, spec.getInParams(), impl.getInParams(), 
				m_SpecificationInParam, m_ImplementationInParam, 
				new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, procId));
		declareParams(procId, spec.getOutParams(), impl.getOutParams(), 
				m_SpecificationOutParam, m_ImplementationOutParam, 
				new DeclarationInformation(StorageClass.IMPLEMENTATION_OUTPARAM, procId));
		declareLocals(impl);
	}
	
	/**
	 * Returns true if spec contains only a specification or impl contains only
	 * an implementation.
	 */
	private boolean isSpecAndImpl(Procedure spec, Procedure impl) {
		return isSpecification(spec) && !isImplementation(spec) && 
				isImplementation(impl) && !isSpecification(impl);
		
	}
	
	public void declareSpec(Procedure spec) {
		assert isSpecification(spec) : "no specification";
		assert !isImplementation(spec) : "is implementation";
		String procId = spec.getIdentifier();
		declareParams(procId, spec.getInParams(), m_SpecificationInParam,
				new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, procId));
		declareParams(procId, spec.getOutParams(), m_SpecificationOutParam,
				new DeclarationInformation(StorageClass.PROC_FUNC_OUTPARAM, procId));
	}
	
	
	private void declareParams(String procId, VarList[] specVl, VarList[] implVl, 
			Map<String, Map<String, BoogieVar>> specMap, 
			Map<String, Map<String, BoogieVar>> implMap,
			DeclarationInformation declarationInformation) {
		if (specVl.length != implVl.length) {
			throw new IllegalArgumentException(
					"specification and implementation have different param length");
		}
		for (int i=0; i<specVl.length; i++) {
			IType specType = specVl[i].getType().getBoogieType();
			IType implType = implVl[i].getType().getBoogieType();
			if (!specType.equals(implType)) {
				throw new IllegalArgumentException(
						"specification and implementation have different types");
			}
			String[] specIds = specVl[i].getIdentifiers();
			String[] implIds = implVl[i].getIdentifiers();
			if (specIds.length != implIds.length) {
				throw new IllegalArgumentException(
						"specification and implementation have different param length");
			}
			for (int j=0; j<specIds.length; j++) {
				BoogieVar bv = constructLocalBoogieVar(implIds[j], procId, 
						implType, implVl[i], declarationInformation);
				putNew(procId, implIds[j], bv, implMap);
				putNew(procId, specIds[j], bv, specMap);
			}
		}
	}
	
	
	/**
	 * Declare in or our parameters of a specification. 
	 * @param procId name of procedure
	 * @param vl Varlist defining the parameters
	 * @param specMap map for the specification
	 * @param declarationInformation StorageClass of the constructed BoogieVar
	 */
	private void declareParams(String procId, VarList[] vl, 
			Map<String, Map<String, BoogieVar>> specMap,
			DeclarationInformation declarationInformation) {
		for (int i=0; i<vl.length; i++) {
			IType type = vl[i].getType().getBoogieType();
			String[] ids = vl[i].getIdentifiers();
			for (int j=0; j<ids.length; j++) {
				BoogieVar bv = constructLocalBoogieVar(ids[j], procId,
						type, vl[i], declarationInformation);
				putNew(procId, ids[j], bv, specMap);
			}
		}
	}
			
			

	public void declareLocals(Procedure proc) {
		if (proc.getBody() != null) {
			DeclarationInformation declarationInformation = 
					new DeclarationInformation(StorageClass.LOCAL, proc.getIdentifier());
			for (VariableDeclaration vdecl : proc.getBody().getLocalVars()) {
				for (VarList vl : vdecl.getVariables()) {
					for (String id : vl.getIdentifiers()) {
						IType type = vl.getType().getBoogieType();
						BoogieVar bv = constructLocalBoogieVar(id, proc.getIdentifier(),
								type, vl, declarationInformation);
						putNew(proc.getIdentifier(), id, bv, m_ImplementationLocals);
					}
				}
			}
		}
	}
	
	
	/**
	 * Construct BoogieVar and store it. Expects that no BoogieVar with the same
	 * identifier has already been constructed.
	 * 
	 * @param identifier
	 * @param procedure
	 * @param iType
	 * @param isOldvar
	 * @param BoogieASTNode
	 *            BoogieASTNode for which errors (e.g., unsupported syntax) are
	 *            reported
	 * @param declarationInformation 
	 */
	private LocalBoogieVar constructLocalBoogieVar(String identifier, 
			String procedure, IType iType, BoogieASTNode BoogieASTNode, 
			DeclarationInformation declarationInformation) {
		Sort sort = m_TypeSortTranslator.getSort(iType, BoogieASTNode);

		String name = constructBoogieVarName(identifier, procedure,
				false, false);

		TermVariable termVariable = m_Script.variable(name, sort);

		ApplicationTerm defaultConstant = constructDefaultConstant(sort, name);
		ApplicationTerm primedConstant = constructPrimedConstant(sort, name);

		LocalBoogieVar bv = new LocalBoogieVar(identifier, procedure, iType,
				termVariable, defaultConstant, primedConstant);
		
		m_SmtVar2BoogieVar.put(termVariable, bv);
		m_BoogieVar2DeclarationInformation.put(bv, declarationInformation);
		return bv;
	}
	
	/**
	 * Construct global BoogieVar and the corresponding oldVar and store both. 
	 * Expects that no local BoogieVarwith the same identifier has already been
	 * constructed.
	 * @param BoogieASTNode
	 *            BoogieASTNode for which errors (e.g., unsupported syntax) are
	 *            reported
	 */
	private BoogieNonOldVar constructGlobalBoogieVar(String identifier,
			IType iType, BoogieASTNode BoogieASTNode) {
		Sort sort = m_TypeSortTranslator.getSort(iType, BoogieASTNode);
		String procedure = null;
		DeclarationInformation declarationInformation = 
				new DeclarationInformation(StorageClass.GLOBAL, null);
		
		BoogieOldVar oldVar;
		{
			boolean isOldVar = true;
			String name = constructBoogieVarName(identifier, procedure,
					true, isOldVar);
			TermVariable termVariable = m_Script.variable(name, sort);
			ApplicationTerm defaultConstant = constructDefaultConstant(sort, name);
			ApplicationTerm primedConstant = constructPrimedConstant(sort, name);

			oldVar = new BoogieOldVar(identifier, iType,
					isOldVar, termVariable, defaultConstant, primedConstant);
			m_SmtVar2BoogieVar.put(termVariable, oldVar);
			m_BoogieVar2DeclarationInformation.put(oldVar, declarationInformation);
		}
		BoogieNonOldVar nonOldVar;
		{
			boolean isOldVar = false;
			String name = constructBoogieVarName(identifier, procedure,
					true, isOldVar);
			TermVariable termVariable = m_Script.variable(name, sort);
			ApplicationTerm defaultConstant = constructDefaultConstant(sort, name);
			ApplicationTerm primedConstant = constructPrimedConstant(sort, name);

			nonOldVar = new BoogieNonOldVar(identifier, iType,
					termVariable, defaultConstant, primedConstant, oldVar);
			m_SmtVar2BoogieVar.put(termVariable, nonOldVar);
			m_BoogieVar2DeclarationInformation.put(nonOldVar, declarationInformation);
		}
		oldVar.setNonOldVar(nonOldVar);
		return nonOldVar;
	}
	

	private ApplicationTerm constructPrimedConstant(Sort sort, String name) {
		ApplicationTerm primedConstant;
		{
			String primedConstantName = "c_" + name + "_primed";
			m_Script.declareFun(primedConstantName, new Sort[0], sort);
			primedConstant = (ApplicationTerm) m_Script.term(primedConstantName);
		}
		return primedConstant;
	}

	private ApplicationTerm constructDefaultConstant(Sort sort, String name) {
		ApplicationTerm defaultConstant;
		{
			String defaultConstantName = "c_" + name;
			m_Script.declareFun(defaultConstantName, new Sort[0], sort);
			defaultConstant = (ApplicationTerm) m_Script.term(defaultConstantName);
		}
		return defaultConstant;
	}

	private String constructBoogieVarName(String identifier, String procedure,
			boolean isGlobal, boolean isOldvar) {
		String name;
		if (isGlobal) {
			assert procedure == null;
			if (isOldvar) {
				name = "old(" + identifier + ")";
			} else {
				name = identifier;
			}
		} else {
			assert (!isOldvar) : "only global vars can be oldvars";
			name = procedure + "_" + identifier;
		}
		return name;
	}
	
	BoogieNonOldVar constructAuxiliaryGlobalBoogieVar(String identifier, String procedure,
			IType iType, BoogieASTNode BoogieASTNode) {
		BoogieNonOldVar bv = constructGlobalBoogieVar(identifier, iType, BoogieASTNode);
		m_Globals.put(identifier, bv);
		m_OldGlobals.put(identifier, bv.getOldVar());
		return bv;
	}
	

}
