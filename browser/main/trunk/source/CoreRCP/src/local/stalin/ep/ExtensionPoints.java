package local.stalin.ep;

/**
 * Class for defining the names of the extension points.
 * Note: Coding Conventions do not apply for the Listing of extension points for better reading in plugin.xml(s)
 * 
 * @author dietsch
 *
 */
public final class ExtensionPoints {
	///////////////////////////////////////////
	//            W A R N I N G              //
	//  When something is renamed in here,   //
	//  it MUSST also be renamed in          //
	//  corresponding plugin.xml(s).         //
	///////////////////////////////////////////	
	
    /**
	 * Extension Point-Name for AST-Generators.
	 */
	public static final String EP_CONTROLLER = "local.stalin.ep.controller";
    
	/**
	 * Extension Point-Name for generative plugins.
	 * They generate a new model out of a present AST.
	 */
	public static final String EP_GENERATOR = "local.stalin.ep.generator";
	
	/**
	 * Extension Point-Name for transforming plugins.
	 */
	public static final String EP_ANALYSIS = 
		"local.stalin.ep.analysis";
	
	/**
	 * Extension Point-Name for Output-Plugins.
	 */
	public static final String EP_OUTPUT = "local.stalin.ep.output";
	
	/**
	 * Extension Point-Name for Source-Plugins.
	 */
	public static final String EP_SOURCE = "local.stalin.ep.source";	
	
	/**
	 * Extension Point-Name for Serialization-Plugins.
	 */
	public static final String EP_SERIALIZATION = "local.stalin.ep.serialization";	
	
	/**
	 * Extensionpoint for LoggingWindow
	 */
	public static final String EP_LOGGINGWINDOW = "local.stalin.ep.LoggingWindow";
	
}
