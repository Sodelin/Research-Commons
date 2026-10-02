// Diagnostic observer for the unchanged public root executor. It adds no DP rules.
#include "part_func.hh"
#include "scfg2/replay/w_final_exact_inside.hh"
#include "ViennaRNA/params/io.h"
#include <fstream>
#include <iomanip>
#include <iostream>
#include <iterator>
#include <unordered_map>
#include <unordered_set>

int main(int argc, char** argv) {
  if (argc != 4) return 2;
  std::ifstream in(argv[3]);
  std::string params((std::istreambuf_iterator<char>(in)), {});
  if (!in || params.empty() || !vrna_params_load_defaults() ||
      !vrna_params_load_from_string(params.c_str(),argv[3],VRNA_PARAMETER_FORMAT_DEFAULT)) return 3;
  std::string sequence=argv[1], scaffold=argv[2];
  W_final_pf owner(sequence,scaffold,true,false,false,2,0.0,0,false);
  owner.reset_exact_chart_storage();
  cparty::scfg2::storage::exact_store::reset();
  namespace s=cparty::scfg2;
  using Key=s::deductions::ItemKey;
  using Ded=s::deductions::Deduction;
  s::replay::WFinalExactInsideContext ctx(owner);
  s::replay::StorageOnlyExactCarrierObserver<s::semirings::SumProductSemiring> carrier(owner);
  std::unordered_map<Key,std::vector<Ded>,s::deductions::ItemKeyHash,s::deductions::ItemKeyEq> active;
  struct Hit { Key key; int k; double local; double child; double contribution; };
  std::vector<Hit> hits;
  std::vector<std::tuple<Ded,double,double>> be_hits;
  const auto chart=s::replay::run_w_final_exact_dp_schedule<s::semirings::SumProductSemiring>(
      s::engine::build_pkfree_basic_exact_schedule(owner.length(),ctx),ctx,
      [](const Ded&){return true;},
      [&](const Key& key,const Ded& d,double contribution,const auto& current,double local) {
        if (contribution>0) {
          active[key].push_back(d);
          if(d.parent.nonterminal==s::grammar::NonTerminal::BE && d.parent.i==d.parent.ip && d.parent.j==d.parent.jp &&
             (d.rule==s::grammar::RuleId::BE_BASE_SAMEPAIR || d.rule==s::grammar::RuleId::BE_STACK))
            be_hits.emplace_back(d,local,contribution);
          if(d.rule==s::grammar::RuleId::VPR_SPLIT_VP_BASEPAIR)
            hits.push_back({key,d.split.k,local,s::replay::runtime_child_total_for_deduction(current,d,0),contribution});
        }
        carrier(key,d,contribution,current,local);
      });
  Key root{s::grammar::NonTerminal::W,1,static_cast<cand_pos_t>(owner.length()),-1,-1};
  std::unordered_set<Key,s::deductions::ItemKeyHash,s::deductions::ItemKeyEq> live;
  std::vector<Key> work{root};
  for(std::size_t h=0;h<work.size();++h) {
    const Key key=work[h];
    if(!live.insert(key).second)continue;
    const auto it=active.find(key);
    if(it==active.end())continue;
    for(const Ded& raw:it->second) {
      const auto d=s::replay::runtime_traceback_deduction(raw);
      for(std::size_t k=0;k<d.child_count;++k)work.push_back(d.children[k].item);
    }
  }
  std::cout<<std::setprecision(17);
  std::cerr<<std::setprecision(17)<<"root\t"<<chart.get(root)<<"\tenergy\t"<<owner.partition_free_energy_from_weight(chart.get(root))
           <<"\tscale\t"<<owner.pf_scale()<<"\tpositive_vpr\t"<<hits.size()<<"\tlive_states\t"<<live.size()<<'\n';
  for(const auto& entry:be_hits) {
    const Ded& d=std::get<0>(entry);
    if(live.count(d.parent)) std::cerr<<"BE_LIVE\t"<<d.parent.i<<'\t'<<d.parent.j<<'\t'<<d.parent.ip<<'\t'<<d.parent.jp<<'\t'<<(d.rule==s::grammar::RuleId::BE_STACK?"STACK":"BASE")<<'\t'<<std::get<1>(entry)<<'\t'<<std::get<2>(entry)<<'\n';
  }
  std::cout<<"i\tj\tk\tactual_padding\texpected_right_padding\tlocal\tchild\tcontribution\n";
  for(const Hit& x:hits)if(live.count(x.key))
    std::cout<<x.key.i<<'\t'<<x.key.j<<'\t'<<x.k<<'\t'<<x.k-x.key.i<<'\t'<<x.key.j-x.k
             <<'\t'<<x.local<<'\t'<<x.child<<'\t'<<x.contribution<<'\n';
}
