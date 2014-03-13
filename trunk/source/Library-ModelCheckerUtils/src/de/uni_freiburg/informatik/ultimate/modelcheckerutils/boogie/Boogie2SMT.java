package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Expression2Term.IdentifierTranslator;
import de.uni_freiburg.informatik.ultimate.result.UnsupportedSyntaxResult;

public class Boogie2SMT {
	
	/**
	 * if set to true array access returns arbitrary values array store returns
	 * arbitrary arrays
	 */
	private final boolean m_BlackHoleArrays;
	
	
	private final BoogieDeclarations m_BoogieDeclarations;
	private Script m_Script;

	private final TypeSortTranslator m_TypeSortTranslator;
	private final Boogie2SmtSymbolTable m_Boogie2SmtSymbolTable;
	private final VariableManager m_VariableManager;
	private final Term2Expression m_Term2Expression;


	private final ConstOnlyIdentifierTranslator m_ConstOnlyIdentifierTranslator;


	public Boogie2SMT(Script script, BoogieDeclarations boogieDeclarations, boolean blackHoleArrays) {
		m_BlackHoleArrays = blackHoleArrays;
		m_BoogieDeclarations = boogieDeclarations;
		m_Script = script;
		m_VariableManager = new VariableManager(m_Script);
		
		m_TypeSortTranslator = new TypeSortTranslator(
				boogieDeclarations.getTypeDeclarations(), m_Script, m_BlackHoleArrays);
		m_Boogie2SmtSymbolTable = new Boogie2SmtSymbolTable(boogieDeclarations, m_Script, m_TypeSortTranslator);
				
		m_ConstOnlyIdentifierTranslator = new ConstOnlyIdentifierTranslator();
		
		for (Axiom decl : boogieDeclarations.getAxioms()) {
			this.declareAxiom(decl);
		}
		
		m_Term2Expression = new Term2Expression(m_TypeSortTranslator, m_Boogie2SmtSymbolTable);

	}
	
	public VariableManager getVariableManager() {
		return m_VariableManager;
	}

	public Script getScript() {
		return m_Script;
	}

	public Term2Expression getTerm2Expression() {
		return m_Term2Expression;
	}
	
	static String quoteId(String id) {
		// return Term.quoteId(id);
		return id;
	}
	
	public Boogie2SmtSymbolTable getBoogie2SmtSymbolTable() {
		return m_Boogie2SmtSymbolTable;
	}
	
	
	
	
	
	public BoogieDeclarations getBoogieDeclarations() {
		return m_BoogieDeclarations;
	}

	public TypeSortTranslator getTypeSortTranslator() {
		return m_TypeSortTranslator;
	}
	
	

	ConstOnlyIdentifierTranslator getConstOnlyIdentifierTranslator() {
		return m_ConstOnlyIdentifierTranslator;
	}



	private void declareAxiom(Axiom ax) {
		IdentifierTranslator[] its = new IdentifierTranslator[]{ getConstOnlyIdentifierTranslator()};
		Term term = (new Expression2Term( its, m_Script, m_TypeSortTranslator, ax.getFormula())).getTerm();
		m_Script.assertTerm(term);
	}
	
	public static void reportUnsupportedSyntax(BoogieASTNode BoogieASTNode, String longDescription) {
		UnsupportedSyntaxResult<BoogieASTNode> result = new UnsupportedSyntaxResult<BoogieASTNode>(BoogieASTNode,
				Activator.s_PLUGIN_NAME,
				UltimateServices.getInstance().getTranslatorSequence(),longDescription);
		UltimateServices.getInstance().reportResult(Activator.s_PLUGIN_NAME, result);
		UltimateServices.getInstance().cancelToolchain();
	}


	
	
	/**
	 * Use with caution! Construct auxiliary variables only if you need then in
	 * the whole verification process.
	 * Construct auxiliary variables only if the assertion stack of the script
	 * is at the lowest level.
	 * Auxiliary variables are not supported in any backtranslation.
	 */
	public BoogieVar constructAuxiliaryBoogieVar(String identifier, 
			String procedure, IType iType, 
			boolean isOldvar, BoogieASTNode BoogieASTNode) {
		return m_Boogie2SmtSymbolTable.constructBoogieVar(identifier, procedure, 
				StorageClass.GLOBAL , iType, isOldvar, BoogieASTNode);
	}
	
	
	class ConstOnlyIdentifierTranslator implements IdentifierTranslator {

		@Override
		public Term getSmtIdentifier(String id,
				DeclarationInformation declInfo, boolean isOldContext,
				BoogieASTNode boogieASTNode) {
			if (declInfo.getStorageClass() != StorageClass.GLOBAL) {
				throw new AssertionError();
			}
			Term result = m_Boogie2SmtSymbolTable.getBoogieConst(id).getSmtConstant();
			if (result == null) {
				throw new AssertionError();
			}
			return result;
		}
	}

}