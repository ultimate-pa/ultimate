package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;

public class Boogie2SmtSymbolTable {
	private final Script m_Script; 
	private final TypeSortTranslator m_TypeSortTranslator;
	private final Map<String, BoogieVar> m_Globals = new HashMap<String, BoogieVar>();
	private final Map<String, BoogieVar> m_OldGlobals = new HashMap<String, BoogieVar>();
	private final Map<String, Map<String, BoogieVar>> m_SpecificationInParam = new HashMap<String, Map<String, BoogieVar>>();
	private final Map<String, Map<String, BoogieVar>> m_SpecificationOutParam = new HashMap<String, Map<String, BoogieVar>>();
	private final Map<String, Map<String, BoogieVar>> m_ImplementationInParam = new HashMap<String, Map<String, BoogieVar>>();
	private final Map<String, Map<String, BoogieVar>> m_ImplementationOutParam = new HashMap<String, Map<String, BoogieVar>>();
	private final Map<String, Map<String, BoogieVar>> m_ImplementationLocals = new HashMap<String, Map<String, BoogieVar>>();
	private final Map<String, BoogieConst> m_Constants = new HashMap<String, BoogieConst>();
	
	private final Map<TermVariable,BoogieVar> m_SmtVar2BoogieVar = new HashMap<TermVariable,BoogieVar>();
	private final Map<ApplicationTerm, BoogieConst> m_SmtConst2BoogieConst = new HashMap<ApplicationTerm,BoogieConst>();
	private Map<String, Procedure> m_Specifications;
	private Map<String, Procedure> m_Implementations;
	
	
	
	
	public Boogie2SmtSymbolTable(Script script,
			TypeSortTranslator typeSortTranslator) {
		super();
		m_Script = script;
		m_TypeSortTranslator = typeSortTranslator;
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
	
	private void putNew(String varId, BoogieVar bv, Map<String, BoogieVar> map) {
		BoogieVar previousValue = map.put(varId, bv);
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
		case PROCEDURE_INPARAM:
//			result = get(varId, procedure, m_SpecificationInParam);
//			break;
		case IMPLEMENTATION_INPARAM:
			result = get(varId, procedure, m_ImplementationInParam);
			break;
		case PROCEDURE_OUTPARAM:
//			result = get(varId, procedure, m_SpecificationOutParam);
//			break;
		case IMPLEMENTATION_OUTPARAM:
			result = get(varId, procedure, m_ImplementationOutParam);
			break;
		case LOCAL:
			result = get(varId, procedure, m_ImplementationLocals);
			break;
		case IMPLEMENTATION:
		case PROCEDURE:
		case QUANTIFIED:
		default:
			throw new AssertionError("inappropriate decl info");
		}
		return result;
	}
	
	public BoogieVar getBoogieVar(TermVariable tv) {
		return m_SmtVar2BoogieVar.get(tv);
	}
	
	
	
	
	public void declareConstants(ConstDeclaration constdecl) {
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
	
	
	public void declareGlobalVariables(VariableDeclaration vardecl) {
		for (VarList vl : vardecl.getVariables()) {
			for (String id : vl.getIdentifiers()) {
				IType type = vl.getType().getBoogieType();
				BoogieVar global = constructBoogieVar(
						id, null, StorageClass.GLOBAL, type, false, vl);
				putNew(id, global, m_Globals);
				BoogieVar oldGlobal = constructBoogieVar(
						id, null, StorageClass.GLOBAL, type, true, vl);
				putNew(id, oldGlobal, m_OldGlobals);
			}
		}
	}
	
	/**
	 * Return global variables;
	 */
	public Map<String, BoogieVar> getGlobals() {
		return Collections.unmodifiableMap(m_Globals);
	}
	
	/**
	 * Return global oldvars;
	 */
	public Map<String, BoogieVar> getOldGlobals() {
		return Collections.unmodifiableMap(m_OldGlobals);
	}
	
	
	public void declareProcedures(Map<String, Procedure> specs, Map<String, Procedure> impls) {
		assert m_Specifications == null && m_Implementations == null : 
			"procedures have already been declared";
		m_Specifications = specs;
		m_Implementations = impls;
		
		Set<String> procIds = new HashSet<String>();
		procIds.addAll(specs.keySet());
		procIds.addAll(impls.keySet());
		for (String procId : procIds) {
			Procedure spec = specs.get(procId);
			Procedure impl = impls.get(procId);
			assert spec != null : "impl without spec not allowed";
			if (impl == null) {
				declareSpec(spec);
			} else {
				declareSpecImpl(spec, impl);
			}
		}
	}
	
	public void declareSpecImpl(Procedure spec, Procedure impl) {
		assert (spec == impl || isSpecAndImpl(spec, impl));
		String procId = spec.getIdentifier();
		assert procId.equals(impl.getIdentifier());
		declareParams(procId, spec.getInParams(), impl.getInParams(), 
				m_SpecificationInParam, m_ImplementationInParam, StorageClass.IMPLEMENTATION_INPARAM);
		declareParams(procId, spec.getOutParams(), impl.getOutParams(), 
				m_SpecificationOutParam, m_ImplementationOutParam, StorageClass.IMPLEMENTATION_OUTPARAM);
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
				StorageClass.PROCEDURE_INPARAM);
		declareParams(procId, spec.getOutParams(), m_SpecificationOutParam,
				StorageClass.PROCEDURE_OUTPARAM);
	}
	
	
	private void declareParams(String procId, VarList[] specVl, VarList[] implVl, 
			Map<String, Map<String, BoogieVar>> specMap, 
			Map<String, Map<String, BoogieVar>> implMap,
			StorageClass storageClassImpl) {
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
				BoogieVar bv = constructBoogieVar(implIds[j], procId, 
						storageClassImpl, implType, false, implVl[i]);
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
	 * @param storageClass StorageClass of the constructed BoogieVar
	 */
	private void declareParams(String procId, VarList[] vl, 
			Map<String, Map<String, BoogieVar>> specMap,
			StorageClass storageClass) {
		for (int i=0; i<vl.length; i++) {
			IType type = vl[i].getType().getBoogieType();
			String[] ids = vl[i].getIdentifiers();
			for (int j=0; j<ids.length; j++) {
				BoogieVar bv = constructBoogieVar(ids[j], procId, storageClass,
						type, false, vl[i]);
				putNew(procId, ids[j], bv, specMap);
			}
		}
	}
			
			

	public void declareLocals(Procedure proc) {
		if (proc.getBody() != null) {
			for (VariableDeclaration vdecl : proc.getBody().getLocalVars()) {
				for (VarList vl : vdecl.getVariables()) {
					for (String id : vl.getIdentifiers()) {
						IType type = vl.getType().getBoogieType();
						BoogieVar bv = constructBoogieVar(id, proc.getIdentifier(),
								StorageClass.LOCAL, type, false, vl);
						putNew(proc.getIdentifier(), id, bv, m_ImplementationLocals);
					}
				}
			}
		}
	}
	
	public Procedure getProcedureSpecification(String procId) {
		assert m_Specifications != null : "Procedure have not yet been declared";
		return m_Specifications.get(procId);
	}
	
	public Procedure getProcedureImplementation(String procId) {
		assert m_Specifications != null : "Procedure have not yet been declared";
		return m_Implementations.get(procId);
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
	 */
	BoogieVar constructBoogieVar(String identifier, String procedure,
			StorageClass storageClass, 
			IType iType, boolean isOldvar, BoogieASTNode BoogieASTNode) {
		Sort sort = m_TypeSortTranslator.getSort(iType, BoogieASTNode);

		String name;
		if (storageClass == StorageClass.GLOBAL) {
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

		TermVariable termVariable = m_Script.variable(name, sort);

		ApplicationTerm defaultConstant;
		{
			String defaultConstantName = "c_" + name;
			m_Script.declareFun(defaultConstantName, new Sort[0], sort);
			defaultConstant = (ApplicationTerm) m_Script.term(defaultConstantName);
		}
		ApplicationTerm primedConstant;
		{
			String primedConstantName = "c_" + name + "_primed";
			m_Script.declareFun(primedConstantName, new Sort[0], sort);
			primedConstant = (ApplicationTerm) m_Script.term(primedConstantName);
		}

		BoogieVar bv = new BoogieVar(identifier, procedure, iType,
				isOldvar, termVariable, defaultConstant, primedConstant);

		if (storageClass == StorageClass.GLOBAL) {
			if (isOldvar) {
//				putNew(identifier, bv, m_OldGlobals);
			} else {
//				putNew(identifier, bv, m_Globals);
			}
		} else if (storageClass == StorageClass.PROCEDURE_INPARAM) {
//			putNew(procedure, identifier, bv, m_SpecificationInParam);
		} else if (storageClass == StorageClass.PROCEDURE_OUTPARAM) {
//			putNew(procedure, identifier, bv, m_SpecificationOutParam);
		} else if (storageClass == StorageClass.IMPLEMENTATION_INPARAM) {
//			putNew(procedure, identifier, bv, m_ImplementationInParam);
		} else if (storageClass == StorageClass.IMPLEMENTATION_OUTPARAM) {
//			putNew(procedure, identifier, bv, m_ImplementationOutParam);
		} else if (storageClass == StorageClass.LOCAL) {
//			putNew(procedure, identifier, bv, m_ImplementationLocals);
		} else {
			throw new AssertionError("unsupported storage classs");
		}
		
		m_SmtVar2BoogieVar.put(termVariable, bv);
		return bv;
	}
	
	

}
