package de.uni_freiburg.informatik.ultimate.LTL2aut;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.HashMap;

import org.apache.commons.io.IOUtils;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.PlatformUI;

import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.AstNode;
import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.AtomicProposition;
import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.model.IElement;

public class DummyLTL2autObserver implements IUnmanagedObserver {

	public AstNode node;
	
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
		try{ //BECAUSE SO!
			
		/*m_FileNames.add(file.getName());
		
		FileInputStream fs = new FileInputStream(file);*/
		String file = "[] a \n a: x > y";
		
		BufferedReader br = new BufferedReader(new InputStreamReader(IOUtils.toInputStream(file)));
		
		//read the LTLT formula and pass it to the parser
		String line = br.readLine();
		
		WrapLTL2Never wrap = new WrapLTL2Never();	
		AstNode node = wrap.ltl2Ast(line);
		
		
		//  get atomic propositions
		HashMap<String, AstNode> aps = new HashMap<String,AstNode>();
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
		//substitute aps
		SubstituteAPVisitor vis = new SubstituteAPVisitor(aps, node);
		
		this.node = node;
		
		}catch(Exception e){}
		
		
		return false;
	}

}
