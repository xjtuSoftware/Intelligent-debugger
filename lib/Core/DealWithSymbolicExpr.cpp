/*
 * SymbolicListener.h
 *
 *  Created on: 2015年7月21日
 *      Author: zhy
 */

#ifndef LIB_CORE_DEALWITHSYMBOLIC_C_
#define LIB_CORE_DEALWITHSYMBOLIC_C_

#define DEBUG 0
#define RANGE 40000

#include "DealWithSymbolicExpr.h"
#include "llvm/IR/Instruction.h"
#include <sstream>
#include <ostream>
#include <set>
#include <vector>
#include <map>

namespace klee {

std::string DealWithSymbolicExpr::getVarName(ref<klee::Expr> value) {
//	std::cerr << "getVarName : " << value << "\n";
	std::stringstream varName;
	varName.str("");
	ReadExpr *revalue;
	if (value->getKind() == Expr::Concat) {
		ConcatExpr *ccvalue = cast<ConcatExpr>(value);
		revalue = cast<ReadExpr>(ccvalue->getKid(0));
	} else if (value->getKind() == Expr::Read) {
		revalue = cast<ReadExpr>(value);
	} else {
		return varName.str();
	}
	std::string globalVarFullName = revalue->updates.root->name;
	unsigned int i = 0;
	while ((globalVarFullName.at(i) != 'S') && (globalVarFullName.at(i) != 'L')) {
		varName << globalVarFullName.at(i);
		i++;
	}
	return varName.str();
}

std::string DealWithSymbolicExpr::getFullName(ref<klee::Expr> value) {

	ReadExpr *revalue;
	if (value->getKind() == Expr::Concat) {
		ConcatExpr *ccvalue = cast<ConcatExpr>(value);
		revalue = cast<ReadExpr>(ccvalue->getKid(0));
	} else if (value->getKind() == Expr::Read) {
		revalue = cast<ReadExpr>(value);
	} else {
		assert( 0 && "getFullName");
	}
	std::string globalVarFullName = revalue->updates.root->name;
	return globalVarFullName;
}

void DealWithSymbolicExpr::resolveSymbolicExpr(ref<klee::Expr> value,
		std::set<std::string>* relatedSymbolicExpr) {
	if (value->getKind() == Expr::Read) {
		std::string varName = getVarName(value);
		if (relatedSymbolicExpr->find(varName) == relatedSymbolicExpr->end()) {
			relatedSymbolicExpr->insert(varName);
		}
		return;
	} else {
		unsigned kidsNum = value->getNumKids();
		if (kidsNum == 2 && value->getKid(0) == value->getKid(1)) {
			resolveSymbolicExpr(value->getKid(0), relatedSymbolicExpr);
		} else {
			for (unsigned int i = 0; i < kidsNum; i++) {
				resolveSymbolicExpr(value->getKid(i), relatedSymbolicExpr);
			}
		}
	}
}

void DealWithSymbolicExpr::addExprToSet(std::set<std::string>* Expr,
		std::set<std::string>* relatedSymbolicExpr) {

	for (std::set<std::string>::iterator it =
			Expr->begin(), ie = Expr->end(); it != ie; ++it) {
		std::string varName =*it;
		if (relatedSymbolicExpr->find(varName) == relatedSymbolicExpr->end()) {
			relatedSymbolicExpr->insert(varName);
		}
	}
}

void DealWithSymbolicExpr::addExprToVector(std::set<std::string>* Expr,
		std::vector<std::string> &relatedSymbolicExpr) {

	for (std::set<std::string>::iterator it =
			Expr->begin(), ie = Expr->end(); it != ie; ++it) {
		std::string varName =*it;
		bool p = true;
		for (std::vector<std::string>::iterator vit =
				relatedSymbolicExpr.begin(), vie = relatedSymbolicExpr.end(); vit != vie; ++vit) {
			if (varName == *vit) {
				p = false;
				break;
			}
		}
		if (p == true) {
			relatedSymbolicExpr.push_back(varName);
		}

	}
}

bool DealWithSymbolicExpr::isRelated(std::string varName) {
	if (allRelatedSymbolicExpr.find(varName) != allRelatedSymbolicExpr.end()) {
		return true;
	} else {
		return false;
	}
}

void DealWithSymbolicExpr::fillterTrace(Trace* trace, std::set<std::string> RelatedSymbolicExpr) {
	std::string varName;

	//PathCondition
	std::vector<ref<klee::Expr> > &usefulStoreSymbolicExpr = trace->usefulStoreSymbolicExpr;
	std::vector<bool > &usefulExpr = trace->usefulExpr;
	usefulExpr.clear();
	for (std::vector<ref<Expr> >::iterator it = usefulStoreSymbolicExpr.begin(), ie =
			usefulStoreSymbolicExpr.end(); it != ie; ++it) {
		varName = getVarName(it->get()->getKid(1));
			usefulExpr.push_back(true);
	}

	//readSet
	std::map<std::string, std::vector<Event *> > &usefulReadSet = trace->usefulReadSet;
	std::map<std::string, std::vector<Event *> > &readSet = trace->readSet;
	usefulReadSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			readSet.begin(), nie = readSet.end(); nit != nie; ++nit) {
			usefulReadSet.insert(*nit);
	}

	//writeSet
	std::map<std::string, std::vector<Event *> > &usefulWriteSet = trace->usefulWriteSet;
	std::map<std::string, std::vector<Event *> > &writeSet = trace->writeSet;
	usefulWriteSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			writeSet.begin(), nie = writeSet.end(); nit != nie; ++nit) {
			usefulWriteSet.insert(*nit);
	}

	//global_variable_initializer
	std::map<std::string, llvm::Constant*> &useful_global_variable_initializer = trace->useful_global_variable_initializer;
	std::map<std::string, llvm::Constant*> &global_variable_initializer = trace->global_variable_initializer;
	useful_global_variable_initializer.clear();
	for (std::map<std::string, llvm::Constant*>::iterator nit =
			global_variable_initializer.begin(), nie = global_variable_initializer.end(); nit != nie; ++nit) {
			useful_global_variable_initializer.insert(*nit);
	}

	//event
	for (std::vector<Event*>::iterator currentEvent = trace->path.begin(), endEvent = trace->path.end();
			currentEvent != endEvent; currentEvent++) {
		if ((*currentEvent)->isGlobal == true) {
					(*currentEvent)->usefulGlobal = true;
		}
	}

	//all_lock_unlock
	std::map<std::string, std::vector<LockPair *> > &all_lock_unlock = trace->all_lock_unlock;
	std::map<std::string, std::vector<LockPair *> > &all_lock_unlock_useful = trace->all_lock_unlock_useful;
	all_lock_unlock_useful.clear();
	for (std::map<std::string, std::vector<LockPair *> >::iterator nit =
			all_lock_unlock.begin(), nie = all_lock_unlock.end(); nit != nie; ++nit) {
		all_lock_unlock_useful.insert(*nit);
	}

	//all_wait
	std::map<std::string, std::vector<Wait_Lock *> > &all_wait = trace->all_wait;
	for (std::map<std::string, std::vector<Wait_Lock *> >::iterator nit =
			all_wait.begin(), nie = all_wait.end(); nit != nie; ++nit) {
		for (std::vector<Wait_Lock *>::iterator it =
				nit->second.begin(), ie = nit->second.end(); it != ie; it++) {
			(*it)->wait->usefulGlobal = false;
		}
	}
	//all_signal
	std::map<std::string, std::vector<Event *> > &all_signal = trace->all_signal;
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			all_signal.begin(), nie = all_signal.end(); nit != nie; ++nit) {
		for (std::vector<Event *>::iterator it =
				nit->second.begin(), ie = nit->second.end(); it != ie; it++) {
			(*it)->usefulGlobal = false;
		}
	}
}

void DealWithSymbolicExpr::fillterTraceAfter(Trace* trace, unsigned eventIdPre, unsigned eventIdPost){

	std::string varName;
	long num = 0;
#if DEBUG
	std::cerr << "\n event id : " << event->eventId << std::endl;
#endif

#if DEBUG
	std::cerr << "\n PathCondition : " << std::endl;
	std::vector<ref<klee::Expr> > &usefulStoreSymbolicExpr = trace->usefulStoreSymbolicExpr;
#endif
	//PathCondition
	std::vector<Event*> &usefulStoreEvent = trace->usefulStoreEvent;
	std::vector<bool > &usefulExpr = trace->usefulExpr;

	long totalExpr = usefulExpr.size();
	for (long i = 0; i <totalExpr; i++) {
//		if (usefulStoreEvent[i]->eventId > event->eventId +RANGE) {
		if (usefulStoreEvent[i]->eventId > eventIdPost) {
			usefulExpr[i] = false;
		}  else {
#if DEBUG
			std::cerr << "eventId : " << usefulStoreEvent[i]->eventId << std::endl;
			std::cerr << "usefulExpr : " << usefulExpr[i] << std::endl;
			std::cerr << "usefulStoreSymbolicExpr : " << usefulStoreSymbolicExpr[i] << std::endl;
#endif
		}
	}

#if DEBUG
	std::cerr << "\n readSet : " << std::endl;
#endif
	//readSet
	std::map<std::string, std::vector<Event *> > &usefulReadSet = trace->usefulReadSet;
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			usefulReadSet.begin(), nie = usefulReadSet.end(); nit != nie; ++nit) {
#if DEBUG
		std::cerr << "\n name : " << nit->first << std::endl;
#endif
		for (std::vector<Event *>::iterator it =
				nit->second.begin(), ie = nit->second.end(); it != ie; ) {
			--ie;
#if DEBUG
			std::cerr << "event id : " << (*ie)->eventId << " name : " << (*ie)->globalVarFullName << std::endl;
#endif
//			if ((*ie)->eventId > event->eventId + RANGE) {
			if ((*ie)->eventId > eventIdPost) {
				(*ie)->usefulGlobal = false;
				nit->second.pop_back();
			} else if ((*ie)->eventId < eventIdPre) {
				(*ie)->usefulGlobal = false;
				nit->second.erase(ie);
			} else {
#if DEBUG
				std::cerr << "usefulGlobal : " << (*ie)->usefulGlobal << std::endl;
#endif
				(*ie)->usefulGlobal =true;
			}
		}
	}

#if DEBUG
	std::cerr << "\n writeSet : " << std::endl;
#endif
	//writeSet
	std::map<std::string, std::vector<Event *> > &usefulWriteSet = trace->usefulWriteSet;
	std::map<std::string, llvm::Constant*> &useful_global_variable_initializer = trace->useful_global_variable_initializer;
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			usefulWriteSet.begin(), nie = usefulWriteSet.end(); nit != nie; ++nit) {
#if DEBUG
		std::cerr << "\n name : " << nit->first << std::endl;
#endif
		num = 0;
		for (std::vector<Event *>::iterator it =
				nit->second.begin(), ie = nit->second.end(); it != ie; ) {
			--ie;
#if DEBUG
			std::cerr << "event id : " << (*ie)->eventId << " name : " << (*ie)->globalVarFullName << std::endl;
#endif
			if ((*ie)->eventId > eventIdPost) {
				(*ie)->usefulGlobal = false;
				nit->second.pop_back();
			} else if ((*ie)->eventId < eventIdPre) {
				if (num == 1) {
					(*ie)->usefulGlobal = false;
					nit->second.erase(ie);
				} else {
					num = 1;
				}
			} else {
#if DEBUG
				std::cerr << "usefulGlobal : " << (*ie)->usefulGlobal << std::endl;
#endif
				(*ie)->usefulGlobal = true;
			}
		}
		if (num == 1) {
			useful_global_variable_initializer.erase(nit->first);
		}
	}

#if DEBUG
	std::cerr << "\n all_lock_unlock : " << std::endl;
#endif
	//all_lock_unlock
	std::map<std::string, std::vector<LockPair *> > &all_lock_unlock = trace->all_lock_unlock;
	for (std::map<std::string, std::vector<LockPair *> >::iterator nit =
			all_lock_unlock.begin(), nie = all_lock_unlock.end(); nit != nie; ++nit) {
#if DEBUG
		std::cerr << "\n name : " << nit->first << std::endl;
#endif
		for (std::vector<LockPair *>::iterator it =
				nit->second.begin(), ie = nit->second.end(); it != ie; ) {
			--ie;
			num = 0;
#if DEBUG
			std::cerr << "lockEvent id : " << (*ie)->lockEvent->eventId << std::endl;
			std::cerr << "unlockEvent id : " << (*ie)->unlockEvent->eventId << std::endl;
#endif
//			if ((*ie)->lockEvent->eventId > event->eventId + RANGE) {
			if ((*ie)->lockEvent->eventId >= eventIdPost) {
				num = 1;
			} else if ((*ie)->unlockEvent->eventId <= eventIdPre) {
				num = 1;
			}
			if (num == 1) {
				(*ie)->lockEvent->usefulGlobal = false;
				(*ie)->unlockEvent->usefulGlobal = false;
				nit->second.erase(ie);
			} else {
				(*ie)->lockEvent->usefulGlobal = true;
				(*ie)->unlockEvent->usefulGlobal = true;
			}
		}
	}

}

void DealWithSymbolicExpr::filterUseless(Trace* trace) {

	std::string varName;
	std::vector<std::string> remainingExprVarName;
	std::vector<ref<klee::Expr> > remainingExpr;
	std::vector<Event*> remainingEvent;
	allRelatedSymbolicExpr.clear();
	remainingExprVarName.clear();
	remainingExpr.clear();
	std::vector<ref<klee::Expr> > &storeSymbolicExpr = trace->storeSymbolicExpr;
	std::vector<Event*> &storeEvent = trace->storeEvent;
	long totalStore = storeSymbolicExpr.size();
	for (long i = 0; i < totalStore; i++) {
		varName = getVarName(storeSymbolicExpr[i]->getKid(1));
		remainingExprVarName.push_back(varName);
		remainingExpr.push_back(storeSymbolicExpr[i]);
		remainingEvent.push_back(storeEvent[i]);
	}
#if DEBUG
		std::cerr << "\n storeSymbolicExpr " << std::endl;
		for (std::vector<ref<Expr> >::iterator it = storeSymbolicExpr.begin(),
				ie = storeSymbolicExpr.end(); it != ie; ++it) {
			std::cerr << *it << std::endl;
		}
#endif


	//br
	std::vector<ref<klee::Expr> > &brSymbolicExpr = trace->brSymbolicExpr;
	std::vector<std::set<std::string>*> &brRelatedSymbolicExpr = trace->brRelatedSymbolicExpr;
	for (std::vector<ref<Expr> >::iterator it = brSymbolicExpr.begin(), ie =
			brSymbolicExpr.end(); it != ie; ++it) {
		std::set<std::string>* tempSymbolicExpr = new std::set<std::string>();
		resolveSymbolicExpr(it->get(), tempSymbolicExpr);
		brRelatedSymbolicExpr.push_back(tempSymbolicExpr);
		addExprToSet(tempSymbolicExpr, &allRelatedSymbolicExpr);
#if DEBUG
		std::cerr << "\n" << *it << "\n brRelatedSymbolicExpr " << std::endl;
		for (std::set<std::string>::iterator it = tempSymbolicExpr->begin(),
				ie = tempSymbolicExpr->end(); it != ie; ++it) {
			std::cerr << *it << std::endl;
		}
#endif
	}

	//assert
	std::vector<ref<klee::Expr> > &assertSymbolicExpr = trace->assertSymbolicExpr;
	std::vector<std::set<std::string>*> &assertRelatedSymbolicExpr = trace->assertRelatedSymbolicExpr;
	for (std::vector<ref<Expr> >::iterator it = assertSymbolicExpr.begin(), ie =
			assertSymbolicExpr.end(); it != ie; ++it) {
		std::set<std::string>* tempSymbolicExpr = new std::set<std::string>();
		resolveSymbolicExpr(it->get(), tempSymbolicExpr);
		assertRelatedSymbolicExpr.push_back(tempSymbolicExpr);
		addExprToSet(tempSymbolicExpr, &allRelatedSymbolicExpr);
#if DEBUG
		std::cerr << "\n" << *it << "\n assertRelatedSymbolicExpr " << std::endl;
		for (std::set<std::string>::iterator it = tempSymbolicExpr->begin(),
				ie = tempSymbolicExpr->end(); it != ie; ++it) {
			std::cerr << *it << std::endl;
		}
#endif
	}

#if DEBUG
	std::cerr << "\n allRelatedSymbolicExpr " << std::endl;
	for (std::set<std::string>::iterator it = allRelatedSymbolicExpr.begin(),
			ie = allRelatedSymbolicExpr.end(); it != ie; ++it) {
		std::cerr << *it << std::endl;
	}
#endif

	std::vector<ref<klee::Expr> > &usefulStoreSymbolicExpr = trace->usefulStoreSymbolicExpr;
	std::vector<Event*> &usefulStoreEvent = trace->usefulStoreEvent;
	std::map<std::string, std::set<std::string>* > &varRelatedSymbolicExpr = trace->varRelatedSymbolicExpr;
	std::vector<std::string> allRelatedSymbolicExprVector;
	addExprToVector(&allRelatedSymbolicExpr, allRelatedSymbolicExprVector);
	unsigned size = allRelatedSymbolicExprVector.size();
	for (unsigned i = 0; i < size; i++) {
		varName = allRelatedSymbolicExprVector[i];
		std::vector<ref<Expr> >::iterator itt = remainingExpr.begin();
		std::vector<Event*>::iterator ittt = remainingEvent.begin();
		for (std::vector<std::string>::iterator it =
				remainingExprVarName.begin();
				it != remainingExprVarName.end();) {
			if (varName == *it) {

				usefulStoreSymbolicExpr.push_back(*itt);
				usefulStoreEvent.push_back(*ittt);

				std::set<std::string>* tempSymbolicExpr = new std::set<std::string>();
				resolveSymbolicExpr(itt->get(), tempSymbolicExpr);
				if (varRelatedSymbolicExpr.find(varName) != varRelatedSymbolicExpr.end()) {
					addExprToSet(tempSymbolicExpr, varRelatedSymbolicExpr[varName]);
				} else {
					varRelatedSymbolicExpr[varName] = tempSymbolicExpr;
				}
				addExprToSet(tempSymbolicExpr, &allRelatedSymbolicExpr);
				addExprToVector(tempSymbolicExpr, allRelatedSymbolicExprVector);
				size = allRelatedSymbolicExprVector.size();
				remainingExprVarName.erase(it);
				remainingExpr.erase(itt);
				remainingEvent.erase(ittt);
			} else {
				++it;
				++itt;
				++ittt;
			}
		}
	}

#if DEBUG
	std::cerr << "\n varRelatedSymbolicExpr " << std::endl;
	for (std::map<std::string, std::set<std::string>* >::iterator nit = varRelatedSymbolicExpr.begin();
			nit != varRelatedSymbolicExpr.end(); ++nit) {
		std::cerr << "name : " << (*nit).first << "\n";
		for (std::set<std::string>::iterator it = (*nit).second->begin(),
				ie = (*nit).second->end(); it != ie; ++it) {
			std::cerr << *it << std::endl;
		}
	}
#endif

	std::map<std::string, long> &varThread = trace->varThread;

	std::map<std::string, std::vector<Event *> > usefulReadSet;
	std::map<std::string, std::vector<Event *> > &readSet = trace->readSet;
	usefulReadSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			readSet.begin(), nie = readSet.end(); nit != nie; ++nit) {
		varName = nit->first;
		if (allRelatedSymbolicExpr.find(varName) != allRelatedSymbolicExpr.end()) {
			usefulReadSet.insert(*nit);
			if (varThread.find(varName) == varThread.end()) {
				varThread[varName] = (*(nit->second.begin()))->threadId;
			}
			long id = varThread[varName];
			if (id != 0){
				for (std::vector<Event *>::iterator it =
						nit->second.begin(), ie = nit->second.end(); it != ie; ++it) {
					if( id != (*it)->threadId){
						varThread[varName] = 0;
						break;
					}
				}
			}

		}

	}
	readSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			usefulReadSet.begin(), nie = usefulReadSet.end(); nit != nie;
			++nit) {
		readSet.insert(*nit);
	}

	std::map<std::string, std::vector<Event *> > usefulWriteSet;
	std::map<std::string, std::vector<Event *> > &writeSet = trace->writeSet;
	usefulWriteSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			writeSet.begin(), nie = writeSet.end(); nit != nie; ++nit) {
		varName = nit->first;
		if (allRelatedSymbolicExpr.find(varName) != allRelatedSymbolicExpr.end()) {
			usefulWriteSet.insert(*nit);
			if (varThread.find(varName) == varThread.end()) {
				varThread[varName] = (*(nit->second.begin()))->threadId;
			}
			long id = varThread[varName];
			if (id != 0){
				for (std::vector<Event *>::iterator it =
						nit->second.begin(), ie = nit->second.end(); it != ie; ++it) {
					if( id != (*it)->threadId){
						varThread[varName] = 0;
						break;
					}
				}
			}
		}
	}
	writeSet.clear();
	for (std::map<std::string, std::vector<Event *> >::iterator nit =
			usefulWriteSet.begin(), nie = usefulWriteSet.end(); nit != nie;
			++nit) {
		writeSet.insert(*nit);
	}

	for (std::map<std::string, long> ::iterator nit = varThread.begin(),
			nie = varThread.end(); nit != nie; ++nit) {
		if (usefulWriteSet.find((*nit).first) == usefulWriteSet.end()) {
			(*nit).second = -1;
		}
	}

#if DEBUG
	std::cerr << "varThread\n";
	for (std::map<std::string, long>::iterator nit =
			varThread.begin(), nie = varThread.end(); nit != nie; ++nit) {
		std::cerr << nit->first << " : " << nit->second << "\n";
	}
#endif

	std::map<std::string, llvm::Constant*> usefulGlobal_variable_initializer;
	std::map<std::string, llvm::Constant*> &global_variable_initializer = trace->global_variable_initializer;
	usefulGlobal_variable_initializer.clear();
	for (std::map<std::string, llvm::Constant*>::iterator nit =
			global_variable_initializer.begin(), nie = global_variable_initializer.end(); nit != nie; ++nit) {
		varName = nit->first;
		if (allRelatedSymbolicExpr.find(varName) != allRelatedSymbolicExpr.end()) {
			usefulGlobal_variable_initializer.insert(*nit);
		}
	}
	global_variable_initializer.clear();
	for (std::map<std::string, llvm::Constant*>::iterator nit =
			usefulGlobal_variable_initializer.begin(), nie = usefulGlobal_variable_initializer.end(); nit != nie;
			++nit) {
		global_variable_initializer.insert(*nit);
	}

//	std::vector<std::vector<Event*>*> eventList = trace->eventList;
	for (std::vector<Event*>::iterator currentEvent = trace->path.begin(), endEvent = trace->path.end();
			currentEvent != endEvent; currentEvent++) {
		if ((*currentEvent)->isGlobal == true) {
			if ((*currentEvent)->inst->inst->getOpcode() == llvm::Instruction::Load
					|| (*currentEvent)->inst->inst->getOpcode() == llvm::Instruction::Store) {
				if (allRelatedSymbolicExpr.find((*currentEvent)->varName) == allRelatedSymbolicExpr.end()) {
					(*currentEvent)->isGlobal = false;
					(*currentEvent)->usefulGlobal = false;
				} else {
					(*currentEvent)->usefulGlobal = true;
				}
			} else {
				(*currentEvent)->usefulGlobal = true;
			}
		}
	}

	std::vector<ref<klee::Expr> > usefulRwSymbolicExpr;
	std::vector<ref<klee::Expr> > &rwSymbolicExpr = trace->rwSymbolicExpr;
	usefulGlobal_variable_initializer.clear();
	for (std::vector<ref<klee::Expr> >::iterator nit =
			rwSymbolicExpr.begin(), nie = rwSymbolicExpr.end(); nit != nie; ++nit) {
		varName = getVarName((*nit)->getKid(1));
		if (allRelatedSymbolicExpr.find(varName) != allRelatedSymbolicExpr.end()) {
			usefulRwSymbolicExpr.push_back(*nit);
		}
	}
	rwSymbolicExpr.clear();
	for (std::vector<ref<klee::Expr> >::iterator nit =
			usefulRwSymbolicExpr.begin(), nie = usefulRwSymbolicExpr.end(); nit != nie;
			++nit) {
		rwSymbolicExpr.push_back(*nit);
	}

	fillterTrace(trace, allRelatedSymbolicExpr);

}

bool DealWithSymbolicExpr::filterUselessWithSet(Trace* trace, std::set<std::string>* relatedSymbolicExpr,
		unsigned eventIdPre, unsigned eventIdPost){
	bool branch = false;
	std::set<std::string> &RelatedSymbolicExpr = trace->RelatedSymbolicExpr;
	RelatedSymbolicExpr.clear();
#if DEBUG
	std::cerr << "\n relatedSymbolicExpr " << std::endl;
	for (std::set<std::string>::iterator it = relatedSymbolicExpr->begin(),
			ie = relatedSymbolicExpr->end(); it != ie; ++it) {
		std::cerr << *it << std::endl;
	}
#endif
	addExprToSet(relatedSymbolicExpr, &RelatedSymbolicExpr);

	std::string varName;
	std::map<std::string, std::set<std::string>* > &varRelatedSymbolicExpr = trace->varRelatedSymbolicExpr;
	std::vector<std::string> RelatedSymbolicExprVector;
	addExprToVector(relatedSymbolicExpr, RelatedSymbolicExprVector);
	unsigned size = RelatedSymbolicExprVector.size();
	for (unsigned i = 0; i < size; i++) {
		varName = RelatedSymbolicExprVector[i];
#if DEBUG
		std::cerr << "\n varName : " <<  varName << std::endl;
#endif
		if (varRelatedSymbolicExpr.find(varName) != varRelatedSymbolicExpr.end()) {
			addExprToSet(varRelatedSymbolicExpr[varName], &RelatedSymbolicExpr);
			addExprToVector(varRelatedSymbolicExpr[varName], RelatedSymbolicExprVector);
			size = RelatedSymbolicExprVector.size();
		}
	}
#if DEBUG
	std::cerr << "\n RelatedSymbolicExpr " << std::endl;
	for (std::set<std::string>::iterator it = RelatedSymbolicExpr.begin(),
			ie = RelatedSymbolicExpr.end(); it != ie; ++it) {
		std::cerr << *it << std::endl;
	}
#endif

	std::map<std::string, long> &varThread = trace->varThread;
	for (std::set<std::string>::iterator it = RelatedSymbolicExpr.begin(),
			ie = RelatedSymbolicExpr.end(); it != ie; ++it) {
		if(varThread[*it] == 0){
			branch = true;
			break;
		}
	}
	if(branch){
		fillterTrace(trace, RelatedSymbolicExpr);
		fillterTraceAfter(trace, eventIdPre, eventIdPost);
		return true;
	}else {
		return false;
	}
}

}

#endif /* LIB_CORE_DEALWITHSYMBOLIC_C_ */
