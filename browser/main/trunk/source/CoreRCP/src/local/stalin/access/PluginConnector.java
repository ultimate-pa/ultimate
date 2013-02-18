package local.stalin.access;

import java.util.ArrayList;
import java.util.List;

import local.stalin.access.walker.CFGWalker;
import local.stalin.access.walker.DFSTreeWalker;
import local.stalin.access.walker.IWalker;
import local.stalin.core.api.StalinServices;
import local.stalin.core.coreplugin.Activator;
import local.stalin.core.coreplugin.Application.Stalin_Mode;
import local.stalin.ep.interfaces.IController;
import local.stalin.ep.interfaces.IGenerator;
import local.stalin.ep.interfaces.ITool;
import local.stalin.model.GraphNotFoundException;
import local.stalin.model.GraphType;
import local.stalin.model.IElement;
import local.stalin.model.IModelManager;
import local.stalin.model.INode;

import org.apache.log4j.Logger;

/**
 * 
 * @author dietsch
 *
 */
public class PluginConnector {
	
	private static Logger s_Logger = StalinServices.getInstance().getLogger(Activator.s_PLUGIN_ID);;
	
	private IModelManager modelManager;
	
	private static IController s_Controller;
	
	private List<IObserver> m_Observers;
	
	private List<GraphType> m_Definition;
	
	private ITool m_Tool;
	
	private boolean m_IsGenerator;
		
	public PluginConnector(IModelManager modelmanager, ITool tool, IController control){
		this.modelManager=modelmanager;
		setController(control);
		m_Tool = tool;
		m_IsGenerator = (tool instanceof IGenerator);
	}

	
	
	private static void setController(IController control){
		s_Controller = control;
	}
	
	
	public void run() throws Exception{
		
		m_Definition = selectModels();
		if(m_Definition.isEmpty()){
			IllegalArgumentException ex = new IllegalArgumentException();
			s_Logger.error("Tool did not select a valid model", ex);
			throw ex;
		}
		m_Tool.setInputDefinition(m_Definition.get(0));
		m_Observers = m_Tool.getObservers();
		
		if(m_IsGenerator){
			runGenerator();
		}
		else {
			runTool();
		}
	}
	
	private void runGenerator(){
		IGenerator tool = (IGenerator)m_Tool;
		for(IObserver observer : m_Observers){
			runObserver(observer);
			retrieveModel(tool,observer.toString());
		}
	}
	
	private void retrieveModel(IGenerator tool, String observer){
		IElement element = tool.getModel();
		if(element instanceof INode)
		{
			INode node = (INode) element;
			GraphType type = tool.getOutputDefinition();
			if (node != null && type != null) {
				modelManager.addItem(node, type);
			} else {
				s_Logger.warn(tool.getName()
						+ " did return invalid model for observer " + observer
						+ ", skipping...");
			}
		}
	}
	
	
	private void runTool(){
		for(IObserver observer : m_Observers){
			runObserver(observer);
		}
	}
	
	private void runObserver(IObserver observer){
		IWalker walker = selectWalker(observer.getWalkerOptions());
		walker.addObserver(observer);
		
		List<INode> entry = getEntryPoints(m_Definition);
		for(int i=0;i<m_Definition.size() && i<entry.size();++i){
			s_Logger.info("Executing an Observer from Plugin " + m_Tool.getName() + " for \""+m_Definition.get(i)+"\" ("+(i+1)+"/"+m_Definition.size()+") ...");
			m_Tool.setInputDefinition(m_Definition.get(i));
			observer.init();
			walker.run(entry.get(i));
			observer.finish();
		}
	}
	
	private List<INode> getEntryPoints(List<GraphType> definition){
		ArrayList<INode> entry = new ArrayList<INode>();
		
		for (GraphType t : definition){
			INode n;
			try {
				n = modelManager.getRootNode(t);
				entry.add(n);
			} catch (GraphNotFoundException e) {
				s_Logger.warn("Graph not found!", e);
			}
			
		}
		return entry;
	}
	
	private List<GraphType> selectModels(){
		List<GraphType> models = new ArrayList<GraphType>();
		switch (m_Tool.getQueryKeyword()) {
		case ALL:
			models = modelManager.getItemKeys();
			break;
		case USER:
			if (modelManager.size() > 1) {
				// In fallback mode, USER == LAST!
				if (StalinServices.getInstance().getStalinMode() == 
					Stalin_Mode.FALLBACK_CMDLINE) {
					models.add(modelManager.getLastAdded());
				} else {
					for (String s : s_Controller.selectModel(modelManager
							.getItemNames())) {
						GraphType t = this.modelManager.getGraphTypeById(s);
						if (t != null) {
							models.add(t);
						}
					}
				}
			} else {
				models.add(modelManager.getItemKeys().get(0));
			}
			break;
		case LAST:
			models.add(modelManager.getLastAdded());
			break;
		case SOURCE:
			models = modelManager.getItemKeys();
			for (GraphType t : models) {
				if (!t.isFromSource()) {
					models.remove(t);
				}
			}
			break;
		case TOOL:
			List<String> desiredToolIDs = m_Tool.getDesiredToolID();
			if (desiredToolIDs == null || desiredToolIDs.size() == 0)
				return models;
			models = modelManager.getItemKeys();
			for (GraphType t : models) {
				if (!desiredToolIDs.contains(t.getCreator()))
					models.remove(t);
			}
			break;
		default:
			s_Logger.fatal("Unknown Query type");
			throw new IllegalStateException("Unknown Query type");
		}
		if (models.isEmpty()) {
			s_Logger
					.warn("no suitable model selected, skipping...");
		}
		return models;
	}
	
	private IWalker selectWalker(WalkerOptions options){
		//TODO implement walker selection logics
		if (this.m_Definition.get(0).getType().name() == "CFG"){
			return new CFGWalker();
		}
		return new DFSTreeWalker();
	}
	
	public boolean hasPerformedChanges() {
		if (this.m_Observers == null) return false;
		boolean res = false;
		for(IObserver observer : m_Observers){
			res = res || observer.performedChanges();
		}
		return res;
	}
	
	public String toString(){
		return m_Tool.getName();
	}
	
}
