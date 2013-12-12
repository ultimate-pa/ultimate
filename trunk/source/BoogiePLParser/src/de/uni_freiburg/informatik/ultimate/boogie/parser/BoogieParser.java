package de.uni_freiburg.informatik.ultimate.boogie.parser;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Level;
import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.model.Payload;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.wrapper.WrapperNode;
import de.uni_freiburg.informatik.ultimate.model.location.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * This is the main Boogie 2 parser class that creates the lexer and parser
 * to parse Boogie 2 files into a CST.
 * 
 * @author hoenicke
 *
 *  $LastChangedRevision: 544 $
 *  $LastChangedDate: 2008-06-05 18:32:43 +0200 (Do, 05 Jun 2008) $
 *  $LastChangedBy: hoenicke $
 *
 */
public class BoogieParser implements ISource {
    protected String[] m_FileTypes;
    protected static Logger s_Logger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);;
    protected List<String> m_FileNames;
    protected Unit m_PreludeUnit;

    public BoogieParser() {
    	m_FileTypes = new String[] { "bpl" };
    	
    }

    /**
     * This method is required by IUltimatePlugin
     * 
     * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IUltimatePlugin#getPluginID()
     */
    public String getPluginID() {
        return Activator.s_PLUGIN_ID;
    }

    /**
     * This initializes the plugin. Parsers usually do not get
     * parameters so we will just return 0 for anything.
     * 
     * @param param is ignored
     * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IUltimatePlugin#init()
     */
    public int init(Object param) {
    	m_FileNames = new ArrayList<String>();
        return 0;
    }

    /**
     * This returns the name of the plugin
     * 
     * @return the name of the plugin
     * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IParser#getName()
     */
    public String getName() {
        return "Boogie PL CUP Parser";
    }

    /**
     * This method uses reflection to return the TokenMap
     * of the special parser
     * 
     * @return the tokens in a map
     * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IParser#getTokens()
     */
    public String[] getTokens() {
    	return new String[] {
            "<invalid>", "<EOR>", "<DOWN>", "<UP>", "TYPE", "ARRAY_TYPE", "GENERIC_TYPE", "UNIT", "VARIABLE_DECLARATION", "TYPE_DECLARATION", "LITERAL", "METHOD", "AXIOM", "PROCEDURE", "BODY", "OPTIDTYPE", "OPTIDTYPELIST", "IDLIST", "CONSTANT", "CONSTANT_UNIQUE", "IDTYPE", "FUNCTION", "PARAMETERS", "RETURN_TYPE", "RETURNS", "VARIABLE", "SIGNATURE", "REQUIRES", "ENSURES", "FREE", "MODIFIES", "IMPLEMENTATION", "IDTYPELIST", "BLOCK", "GOTO", "RETURN", "ASSIGN", "LEFTHANDSIDE", "ASSIGNEXPRESSION", "ARRAYASSIGN", "CALL", "ASSERT", "ASSUME", "HAVOC", "INDEX", "EQUIVALENCE", "IMPLICATION", "ANDEXPR", "OREXPR", "RELATION", "TERM", "EXPRESSIONLIST", "DECIMAL_LITERAL", "BOOLEAN_LITERAL", "INT_LITERAL", "NOT", "NEG", "BV_LITERAL", "STRING_LITERAL", "CHAR_LITERAL", "HEX_LITERAL", "OCT_LITERAL", "NULL", "ARRAYEXPR", "ATOM", "ARITHMUL", "ARITHDIV", "ARITHMOD", "ARITHMINUS", "ARITHPLUS", "COMPEQ", "COMPNEQ", "COMPLT", "COMPLEQ", "COMPGT", "COMPGEQ", "COMPPARTORDER", "ID", "OLD", "CAST", "FORALL", "EXISTS", "TYPEID", "VARID", "Id", "BitvecLiteral", "IntegerLiteral", "BooleanLiteral", "WS", "COMMENT", "ATTTRIBUTES", "LINE_COMMENT", "IdCharacter", "Digit", "Number", "'bool'", "'int'", "'ref'", "'name'", "'any'", "'['", "','", "']'", "'<'", "'>'", "'type'", "';'", "'const'", "'unique'", "':'", "'function'", "'('", "')'", "'returns'", "'axiom'", "'var'", "'procedure'", "'free'", "'requires'", "'modifies'", "'ensures'", "'implementation'", "'{'", "'}'", "'goto'", "'return'", "':='", "'assert'", "'assume'", "'havoc'", "'call'", "'<==>'", "'==>'", "'&&'", "'||'", "'!'", "'-'", "'null'", "'old'", "'cast'", "'::'", "'=='", "'!='", "'>='", "'<='", "'<:'", "'+'", "'*'", "'/'", "'%'", "'forall'", "'exists'"
        };
	}

    /**
	 * Parses a list of files and constructs a tree with root node "PROJECT".
	 * This function uses reflection to get the parser, so make sure you set
	 * the correct one in your parser
	 * 
	 * @param files an array of files to be parsed
	 * @return the tree
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IParser#parseAST(java.io.File[])
	 */
    public INode parseAST(File[] files) throws IOException {
        Payload p = new Payload(null, "PROJECT");
        INode tree = new TreeNode(p);

        for (File f : files) {
            INode node = parseAST(f);
            tree.addOutgoingNode(node);
        }
//        return cleanTree(tree);
        return tree;
    }

    /**
	 * Parses a file and constructs a tree.
	 * This function uses reflection to get the parser, so make sure you set
	 * the correct one in your parser
	 * 
	 * @param file a file to be parsed
	 * @return the tree
     * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IParser#parseAST(java.io.File)
     */
    public INode parseAST(File file) throws IOException {
    	m_FileNames = new ArrayList<String>();
        INode tree = parseDir(file);
        return tree;
    }
    
    private INode parseDir(File file) throws IOException {
        if (file.isDirectory()) {
            Payload p = new Payload(null, "PROJECT");
            INode tree = new TreeNode(p);

            for (File f : file.listFiles()) {
                INode node = parseAST(f);
                tree.addOutgoingNode(node);
            }
            return tree;
        } else {
            return parseFile(file);
        }
    }
    
    private INode parseFile(File file) throws IOException {
        s_Logger.info("Parsing: '"+file.getAbsolutePath()+"'");
        m_FileNames.add(file.getAbsolutePath());
        INode in = reflectiveParse(file.getAbsolutePath());
        return in;
    }
    
   
    private List<INode> getUnits(INode tree) {
        List<INode> returnList = new ArrayList<INode>();
        if(tree.getPayload().getName()=="PROJECT") {
            for(INode n : tree.getOutgoingNodes()) {
                returnList.addAll(getUnits(n));
            }
            return returnList;
        } else {
            returnList.add(tree);
            return returnList;
        }
    }

    /**
     * Gets a list of files and checks whether all of them are
     * parseable by this parser.
     * 
     * @param files a list of files to check
     * @return true if parseable
     * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IParser#parseable(java.io.File[])
     */
    public boolean parseable(File[] files) {
        for (File f : files) {
            if (!parseable(f)) { return false; }
        }
        return true;
    }

    /**
     * Gets a file and checks whether it is
     * parseable by this parser. 
     * 
     * @param file the file to be checked
     * @return true if parseable
     * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IParser#parseable(java.io.File)
     */
    public boolean parseable(File file) {
    	for(String s : getFileTypes())
    	{
    		if(file.getName().endsWith(s))
    			return true;
    	}
        return false;
    }

    /**
     * get all supported file types of this parser
     */
    public String[] getFileTypes() {
        return m_FileTypes;
    }
    

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.ep.interfaces.IOutputDefinition#getOutputDefinition()
	 */
	public GraphType getOutputDefinition() {
		try {
			return new GraphType(getPluginID(), GraphType.Type.AST,this.m_FileNames);
		} catch (Exception ex) {
			s_Logger.log(Level.FATAL,"syntax error: " + ex.getMessage());
			return null;
		}
	}
	
	/**
	 * This function parses the file given as argument. It is quite flexible so
	 * be careful using it
	 * 
	 * @param fileName
	 *            the file to be parsed
	 * @return an INode containing the AST
	 */
	private INode reflectiveParse(String fileName) throws IOException
	{
		BoogieSymbolFactory symFactory = new BoogieSymbolFactory();
		Lexer lexer;
		Parser parser;
		Unit mainFile;
		
		lexer = new Lexer(new FileInputStream(fileName));
		lexer.setSymbolFactory(symFactory);
		parser = new Parser(lexer, symFactory);
		parser.setFileName(fileName);
		try {
			mainFile = (Unit) parser.parse().value;
		} catch (Exception e) {
			s_Logger.fatal("syntax error: ", e);
			// TODO: Declare to throw a parser exception 
			throw new RuntimeException(e);
		}
		if (m_PreludeUnit != null) {
			Declaration[] prel = m_PreludeUnit.getDeclarations();
			Declaration[] main = mainFile.getDeclarations();
			Declaration[] allDecls = new Declaration[prel.length + main.length];
			System.arraycopy(prel, 0, allDecls, 0, prel.length);
			System.arraycopy(main, 0, allDecls, prel.length, main.length);
			ILocation dummyLocation = 
					new BoogieLocation(parser.filename, -1,-1,-1,-1, false);
			mainFile = new Unit(dummyLocation, allDecls);
		}
		return new WrapperNode(null, mainFile);
	}

	@Override
	public void setPreludeFile(File prelude) {
		m_PreludeUnit = null;
		if (prelude == null)
			return;
		try {
			BoogieSymbolFactory symFactory = new BoogieSymbolFactory();
			Lexer lexer = new Lexer(new FileInputStream(prelude));
			lexer.setSymbolFactory(symFactory);
			Parser parser = new Parser(lexer, symFactory);
			parser.setFileName(prelude.getPath());
			m_PreludeUnit = (Unit) parser.parse().value;
		} catch (Exception e) {
			s_Logger.fatal("syntax error: ", e);
			throw new RuntimeException(e);
		}
	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		// TODO Auto-generated method stub
		return null;
	}
}
