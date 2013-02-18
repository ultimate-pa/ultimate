package de.uni_freiburg.informatik.ultimate.core.coreplugin;

import java.util.ArrayList;
import java.util.Date;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

import org.apache.log4j.Logger;

/**
 * 
 * This class should provide timing functions to measure runtime and perhaps other aspects of tool and parser performance
 * 
 * still under construction
 * 
 * @author dietsch
 *
 */
public class Benchmark {
	
	private Date m_StartDate;
	private Date m_StopDate;
	private Date m_PauseDate;
	private long m_Elapsed;
	private String m_Title;
	private ArrayList<String> m_Output;
	private static Logger s_Logger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID); 
	
	public Benchmark(){
		m_Output = new ArrayList<String>();
	}
	
	public void start(String title){
		m_StartDate = new Date();
		m_PauseDate = m_StartDate;
		m_Title = title;
	}
	
	public void stop(){
		if(m_StartDate == null){
			s_Logger.warn("call Start() first !");
			return;
		}
		m_StopDate = new Date();
		m_Elapsed = m_Elapsed + (m_StopDate.getTime() - m_PauseDate.getTime());
		m_Output.add(m_Title+" took "+m_Elapsed+"ms");
		this.reset();
	}
	
	public void reset(){
		m_StartDate = null;
		m_StopDate = null;
		m_PauseDate = null;
		m_Elapsed = 0;
	}
	
	public void pause(){
		if(m_StartDate == null){
			s_Logger.warn("call Start() first !");
			return;
		}
		Date date = new Date();
		m_Elapsed = m_Elapsed + (date.getTime() - m_PauseDate.getTime());
		m_PauseDate = date;
	}
	
	public void unpause(){
		m_PauseDate = new Date();
	}
	
	public void report(){
		for(String s : m_Output){
			s_Logger.info(s);
		}
		m_Output = new ArrayList<String>();
	}
	
	public String toString(){
		StringBuilder builder = new StringBuilder();
		for (String s : m_Output){
			builder.append(s+"\n");
		}
		return builder.toString();
	}
}
