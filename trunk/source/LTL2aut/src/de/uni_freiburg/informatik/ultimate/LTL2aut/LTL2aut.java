package de.uni_freiburg.informatik.ultimate.LTL2aut;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Dictionary;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.commons.io.IOUtils;
import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.AstNode;
import de.uni_freiburg.informatik.ultimate.LTL2aut.ast.AtomicProposition;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.TokenMap;

public class LTL2aut implements ISource {
	
	 protected static Logger Logger = UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);

	 protected List<String> m_FileNames = new ArrayList<String>();
	 
	@Override
	public int init(Object params) {
		// TODO Auto-generated method stub
		return 0;
	} 

	@Override
	public String getName() {
		 return Activator.PLUGIN_ID;
	}

	@Override
	public String getPluginID() {
		 return Activator.PLUGIN_ID;
	}

	@Override
	public boolean parseable(File[] files) {
        for (File f : files) {
            if (!parseable(f)) { return false; }
        }
        return true;
	}

	@Override
	public boolean parseable(File file) {
		for(String s : getFileTypes())
    	{
    		if(file.getName().endsWith(s))
    			return true;
    	}
        return false;
	}

	@Override
	public IElement parseAST(File[] files) throws Exception {
		return this.parseAST(files[0]);
	}

	@Override
	public IElement parseAST(File file) throws Exception { 
		m_FileNames.add(file.getName());
		
		FileInputStream fs = new FileInputStream(file);
		BufferedReader br = new BufferedReader(new InputStreamReader(fs));
		
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
		
		return node;
	}

	@Override
	public String[] getTokens() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String[] getFileTypes() {
		return new String[]{"ltl"};
	}

	@Override
	public TokenMap getTokenMap() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public GraphType getOutputDefinition() {
		return new GraphType(getPluginID(), GraphType.Type.AST,this.m_FileNames);
	}

	@Override
	public void setPreludeFile(File prelude) {
		// TODO Auto-generated method stub
		
	}

}
