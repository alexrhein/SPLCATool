/*******************************************************************************
 * Copyright (c) 2011, 2012 SINTEF, Martin F. Johansen.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     SINTEF, Martin F. Johansen - the implementation
 *******************************************************************************/
package no.sintef.ict.splcatool;

import java.io.File;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.TimeoutException;

import org.sat4j.core.VecInt;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IVecInt;

import splar.core.constraints.BooleanVariableInterface;

public class CoveringArrayAlgAllSat extends CoveringArray {

	private CNF cnf;
	private long coverage = 0;
	
	private List<List<Integer>> result;
	private List<Integer> nrs = null;

	// Invalid tuples sets
	private Set<Pair> invalid1w;
	private Set<Pair2> invalid2w;
	private Set<Pair3> invalid3w;
	private File fmdir;

	public CoveringArrayAlgAllSat(CNF cnf, Map<Integer, String> nrid, Map<String, Integer> idnr) {
		this.cnf = cnf;
		this.nrid = nrid;
		this.idnr = idnr;
	}

	public long getCoverage(){
		return(coverage);
	}

	@Override
	public void generate(int coverLimit, Integer sizelimit) throws TimeoutException {
		try {
			generate2(coverLimit, sizelimit);
		} catch (org.sat4j.specs.TimeoutException e) {
			throw new TimeoutException();
		}
	}

	@Override
	public void generate() throws TimeoutException {
		generate(100, Integer.MAX_VALUE);
	}
	
	@Override
		public Integer[] getRow(int n) {
			if(nrs == null){
				nrs = new ArrayList<Integer>(nrid.keySet());
				Collections.sort(nrs);
			}
			
			List<Integer> nl = result.get(n);
			Integer[] res = new Integer[nl.size()];
			
	/*		if(nl.size() != nrs.size()){
				System.out.println("Incompatible sizes: " + nl.size() + " and " + nrs.size());
				System.exit(-1);
			}
	*/		
			for(int i = 0; i < nrs.size(); i++){
				int x = nrs.get(i);
				for(int j = 0; j < nl.size(); j++){
					if(Math.abs(nl.get(j)) == x)
						res[i] = nl.get(j)<0?1:0;
				}
			}
	
			return res;
		}

	@Override
	public int getRowCount() {
		return result.size();
	}

	@Override
	public void setTimeout(int timeout) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public double estimateGenerationTime() {
		int F = cnf.getFocusVariables().size();
		
		if(t == 2) return Math.exp(0.52*Math.log(F) + 0.80);
		if(t == 3) return Math.exp(0.69*Math.log(F) + 1.25);
		
		throw new UnsupportedOperationException();
	}

	@Override
	public String getAlgorithmName() {
		return "AllSat";
	}

	private void generate2(int coverLimit, Integer sizelimit) throws TimeoutException, org.sat4j.specs.TimeoutException{
		
        // Get a list of vars
		List<BooleanVariableInterface> vars = new ArrayList<BooleanVariableInterface>(cnf.getFocusVariables());
		int numfocusVars = vars.size();
		
		SAT4JSolver satSolver;
		try {
			satSolver = cnf.getSAT4JSolver();
		} catch (ContradictionException e) {
			e.printStackTrace();
			return;
		}
		
		// Solutions
		List<BitSet> solutions = new LinkedList<BitSet>();
		{
			BitSet t1 = new BitSet(numfocusVars); // bit 1 is set
			t1.set(1);
			BitSet f1 = new BitSet(numfocusVars); // bit 1 is not set
			solutions.add(t1);
			solutions.add(f1);
		}
		for (int varid = 2; varid < vars.size(); varid++) {
			// varid is the new variable in this round
			System.out.println("Round " + varid + " starting with " + solutions.size() + " solutions.");
			List<BitSet> newSolutions = new LinkedList<BitSet>(); // new Solutions from this round
			Iterator<BitSet> solutionsIter = solutions.iterator();
			while (solutionsIter.hasNext()) {
				BitSet solution = solutionsIter.next();
				// assumpsArray[0] -> VariableID 1; assumpsArray[1] -> VariableID 2; ... 
				int assumpsArray[] = new int[varid];
				for(int i = 0; i < varid; i++) {
					assumpsArray[i] = (solution.get(i+1) ? (i+1) : -(i+1));
				}
				assumpsArray[varid-1] = varid;
				IVecInt assumps = new VecInt(assumpsArray);
				boolean settingIsPossible = false;
				// Check
				if(satSolver.solver.isSatisfiable(assumps)){
					settingIsPossible = true;
				}
				assumpsArray[varid-1] = -varid;
				assumps = new VecInt(assumpsArray);
				boolean unsettingIsPossible = false;
				// Check
				if(satSolver.solver.isSatisfiable(assumps)){
					unsettingIsPossible = true;
				}
				if (settingIsPossible && unsettingIsPossible) {
					// both; reuse solution and add one new solution
					BitSet newSol = (BitSet) solution.clone();
					solution.set(varid);
					assert (newSol.get(varid)==false);
					newSolutions.add(newSol);
				} else if (settingIsPossible && !unsettingIsPossible) {
					// only setting; reuse solution
					solution.set(varid);
				} else if (!settingIsPossible && unsettingIsPossible) {
					// only unsetting; reuse solution
					solution.clear(varid);
				} else {
					// both are impossible
					solutionsIter.remove();
				}
			}
			solutions.addAll(newSolutions);
		}
		System.out.println("Solutions: " + solutions.size());
		result = new ArrayList<>(solutions.size());
		Iterator<BitSet> iter = solutions.iterator();
		while (iter.hasNext()) {
			BitSet sol = iter.next();
			iter.remove();
			ArrayList<Integer> solLst = new ArrayList<>(numfocusVars);
			for (int i = 1; i < numfocusVars+1; i++) {
				if (sol.get(i))
					solLst.add(i);
			}
			result.add(solLst);
		}
	}

	private List<Pair2> getInvalid(int coveredInitially, List<Pair2> uncovered) {
		int uncTotal = uncovered.size() + coveredInitially;
		
		// This should run
		Runtime runtime = Runtime.getRuntime();        
        int threads = runtime.availableProcessors();
        System.out.println("Threads for this task: " + threads);
		
		// Remove invalid
		List<List<Pair2>> uncSplit = new ArrayList<List<Pair2>>();
		int beg=0, range=uncovered.size()/threads + 1;
		for(int i = 0; i < threads; i++){
			if(beg+range > uncovered.size()) range = uncovered.size() - beg;
			uncSplit.add(uncovered.subList(beg, beg+range));
			//System.out.println(beg + " ->" + (beg+range));
			beg += range;
		}

		List<RIThread> rits = new ArrayList<RIThread>();
		List<Thread> ts = new ArrayList<Thread>();
		for(int i = 0; i < threads; i++){
			RIThread rit = new RIThread(cnf, uncSplit.get(i), nrid, idnr);
			rits.add(rit);
			Thread t = new Thread(rit);
			ts.add(t);
		}
		
		for(int i = 0; i < threads; i++){
			ts.get(i).start();
		}
		
		// Start monitoring thread
		List<ProgressReporter> prs = new ArrayList<ProgressReporter>(rits);
		ProgressThread pt = new ProgressThread("Find invalid pairs", prs, uncTotal);
		Thread ptt = new Thread(pt);
		ptt.start();
		
		// Wait for all threads to finish
		for(int i = 0; i < threads; i++){
			try {
				ts.get(i).join();
			} catch (InterruptedException e) {
			}
		}
		
		// Stop monitoring
		pt.stop();
		
		// Collect
		uncovered = new ArrayList<Pair2>();
		for(int i = 0; i < threads; i++){
			uncovered.addAll(rits.get(i).getValid());
		}
		
		// Return
		return uncovered;
	}

	private List<Pair3> getInvalid3(int coveredInitially, List<Pair3> uncovered) {
		int uncTotal = uncovered.size() + coveredInitially;
		
		// This should run
		Runtime runtime = Runtime.getRuntime();        
	    int threads = runtime.availableProcessors();
	    System.out.println("Threads for this task: " + threads);
		
		// Remove invalid
		List<List<Pair3>> uncSplit = new ArrayList<List<Pair3>>();
		int beg=0, range=uncovered.size()/threads + 1;
		for(int i = 0; i < threads; i++){
			if(beg+range > uncovered.size()) range = uncovered.size() - beg;
			uncSplit.add(uncovered.subList(beg, beg+range));
			//System.out.println(beg + " ->" + (beg+range));
			beg += range;
		}
	
		List<RIThread3> rits = new ArrayList<RIThread3>();
		List<Thread> ts = new ArrayList<Thread>();
		for(int i = 0; i < threads; i++){
			RIThread3 rit = new RIThread3(cnf, uncSplit.get(i), nrid, idnr);
			rits.add(rit);
			Thread t = new Thread(rit);
			ts.add(t);
		}
		
		for(int i = 0; i < threads; i++){
			ts.get(i).start();
		}
		
		// Start monitoring thread
		List<ProgressReporter> prs = new ArrayList<ProgressReporter>(rits);
		ProgressThread pt = new ProgressThread("Find invalid", prs, uncTotal);
		Thread ptt = new Thread(pt);
		ptt.start();
		
		// Wait for all threads to finish
		for(int i = 0; i < threads; i++){
			try {
				ts.get(i).join();
			} catch (InterruptedException e) {
			}
		}
		
		// Stop monitoring
		pt.stop();
		
		// Collect
		uncovered = new ArrayList<Pair3>();
		for(int i = 0; i < threads; i++){
			uncovered.addAll(rits.get(i).getValid());
		}
		
		for(int i = 0; i < threads; i++){
			invalid3w.addAll(rits.get(i).getInvalid());
		}
		
		// Return
		return uncovered;
	}

	private List<Pair> getCovered(List<Integer> solution, List<BooleanVariableInterface> vars) {
		List<Pair> covered = new ArrayList<Pair>();
		
		for(int i = 0; i < solution.size(); i++){
			Pair pair = new Pair();
			int p = solution.get(i);
			for(BooleanVariableInterface var : vars){
				if(var.getID().equals(nrid.get(Math.abs(p)))){
					pair.v = var;
					pair.b = p>0;
				}
			}
			if(pair.v != null)
				covered.add(pair);
		}
		return covered;
	}
}