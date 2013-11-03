package de.uni_freiburg.informatik.ultimate.LTL2aut;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.util.HashMap;

import org.apache.commons.io.IOUtils;

import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.AstNode;
import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.AtomicProposition;
import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.model.IElement;


/**
 * This class reads a definition of a property in ltl and returns 
 * the AST of the description of the LTL formula as a Buchi automaton.
 * 
 * @author Langenfeld
 *
 */
public class DummyLTL2autObserver implements IUnmanagedObserver {

	public AstNode rootNode;
	
	@Override
	public void init() {
		// TODO Auto-generated method stub

	}

	@Override
	public void finish() {
		// TODO Auto-generated method stub

	}

	@Override
	public WalkerOptions getWalkerOptions() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean process(IElement root) {
				
		//code for parsing of input file if this is going to be a source plugin
		/*m_FileNames.add(file.getName());
		FileInputStream fs = new FileInputStream(file);*/
			
		//String fileContent = "a U [] b \n a: x > y";
		//String fileContent = "a U [] b";
		String fileContent = "[] a";
		
		AstNode node;
		String line;
		
		BufferedReader br = new BufferedReader(new InputStreamReader(IOUtils.toInputStream(fileContent)));
		try{	
			//read the LTLT formula from the first line and pass it to the parser
			line = br.readLine();
	
			//translate to ba with external tool and get AST
			WrapLTL2Never wrap = new WrapLTL2Never();	
			node = wrap.ltl2Ast(line);
		}catch(Exception e){
			System.out.println("Something went wrong with ltl2aut");
			//TODO: log error to console (not implemented because logger breaks tests, rethrowing error breaks interface!)
			return false;
		}
			
		try{
			//Read following lines and get Atomic Props
			HashMap<String, AstNode> aps = new HashMap<String,AstNode>(); //ident -> propostition
			line = br.readLine(); 
			while(line != null){
				LexerAP lexer = new LexerAP(new InputStreamReader(IOUtils.toInputStream(line)));
				parserAP p = new parserAP(lexer);
				AstNode nodea = (AstNode)p.parse().value;			
				// append node to dictionary of atomic propositions
				if (nodea instanceof AtomicProposition)
					aps.put(((AtomicProposition) nodea).getIdent(), nodea.getOutgoingNodes().get(0));
				
				line = br.readLine();
			}
			//substitute props in AST
			SubstituteAPVisitor vis = new SubstituteAPVisitor(aps, node);
			
			this.rootNode = node;
			
		}catch(Exception e){
			System.out.println("Something went wrong parsing");
			//TODO: log error to console (not implemented because logger breaks tests, rethrowing error breaks interface!)
			return false;
		}
		
		
		return false;
	}

}
