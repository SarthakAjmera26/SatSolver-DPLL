using namespace std;
#include<bits/stdc++.h>
#define all(x) x.begin(), x.end()
#define literal vector<int>
#define clause  vector< vector<int> >
#define printclock cerr<<"Time : "<<1000*(long double)clock()/(long double)CLOCKS_PER_SEC<<"ms\n";

const int N = 4;
const int M = 4;
 
bool breeze,stench;

int dx[]={1,-1,0,0};
int dy[]={0,0,1,-1};

//information about explored cells
int reached[5][5];
int cur_x = 1;
int cur_y = 1;

//the grid which holds representation of wumpus world
char mat[5][5];

//int dpll_calls
int dpll_calls = 0;

bool valid(int xx, int yy)
{
	if ( xx<1 || yy<1 || xx>N || yy>M )
		return false;
 
	return true;
}
 
void printLiteral(vector<int>lit)
{
	for (int i = 0; i<4; ++i)
	{
		if ( i == 0 )
			cout<<"{";
 
		if (i!=1 || lit[i]<=0)
		cout<<lit[i];
		else
		cout<<(char)lit[i];
		if (i!=3)
			cout<<",";
		else
			cout<<"}";
	}
}
 
void printClause(vector<literal>cla)
{
	for ( int i = 0; i<cla.size(); ++i )
	{
		if ( i == 0 )
			cout<<"[ ";
 
		printLiteral(cla[i]);
 
		if ( i!=cla.size()-1 )
			cout<<", ";
 
		else
			cout<<" ]";
		
	}
}
 
void printKB(vector<clause>KB)
{
	for ( int i = 0; i<KB.size(); ++i )
	{
		if ( i == 0 )
			cout<<"|| \n";
 
		printClause(KB[i]);
 
		if ( i!=KB.size()-1 )
			cout<<", ";
 
		else
			cout<<" ||";
		
		cout<<"\n";
	}	
}
 
vector<vector<int>> erase1( vector<vector<int>>argu, map<int,int>idx  )
{
	int cur_idx = argu.size() - 1;
	vector<vector<int>>res;
 
	while( cur_idx>=0 )
	{
		if (!idx[ cur_idx ])
			res.push_back(argu.back());
		
 
		argu.pop_back();
		--cur_idx;
	}
 
	reverse(all(res));
	return res;
}
 
vector<vector<vector<int>>> erase2( vector<vector<vector<int>>>argu, map<int,int>idx  )
{
	int cur_idx = argu.size() - 1;
	vector<vector<vector<int>>>res;
 
	while( cur_idx>=0 )
	{
		if (!idx[ cur_idx ])
			res.push_back( argu.back() );
 
		argu.pop_back();
		--cur_idx;
	}
	reverse(all(res));
	return res;
}

vector< pair<int,int>> findPath(int ix, int iy, int fx, int fy)
{
	vector< pair<int,int> >res;
	queue<int>nodex,nodey;
	int vis[5][5]={0};
	pair<int,int> par[5][5];

	nodex.push(ix);
	nodey.push(iy);
	vis[ix][iy] = 1;
	par[ix][iy]={0,0};

	while(nodex.size())
	{
		int cx = nodex.front();
		int cy = nodey.front();

		nodex.pop();
		nodey.pop();

		for ( int i = 0; i<4; ++i )
		{
			int nx = dx[i] + cx;
			int ny = dy[i] + cy;

			if ( !valid(nx,ny) || vis[nx][ny] || !reached[nx][ny] )
				continue;

			par[nx][ny] = {cx,cy};
			vis[nx][ny] = 1;
			nodex.push(nx);
			nodey.push(ny);
		}
	}

	int cx = fx;
	int cy = fy;

	while(cx)
	{
		res.push_back({cx,cy});
		pair<int,int>temp = par[cx][cy];
		cx = temp.first;
		cy = temp.second;
	}

	reverse(all(res));
	return res;
}

vector<clause> updateKB( vector< clause >KB, literal upd)
{
	map<int,int>master;
 
	for ( int i = 0; i<KB.size(); ++i )
	{
		bool match = false;
		bool dematch = false;
 
		map<int,int>sub;
 
		for ( int j = 0; j<KB[i].size(); ++j )
		{
			if ( KB[i][j][1] == upd[1] && KB[i][j][2] == upd[2] && KB[i][j][3] == upd[3] )
			{
				if ( KB[i][j][0] == upd[0] )
					match = true;
 
				else
				{
					dematch = true;
					sub[j] = 1;
				}
			}
		}
 
		if ( match )
			master[i]=1;
 
		else
		{
			KB[i] = erase1(KB[i], sub);
		}
	}
 
	KB = erase2(KB,master);
 
	return KB;
}
 
bool DPLL( vector<clause>KB, vector<literal>left )
{
	++dpll_calls;

	//early termination heuristic
	for ( auto it : KB )
		if ( it.size() == 0 )
			return false;
	
	//if all clauses are satisifed, return true 
	if (KB.size() == 0)
		return true;
 	
 	//line 229 - 241 contains unit clause heuristic
	vector<literal>unit_clauses;
 
	for ( auto it : KB )
	{
		if ( it.size() == 1 )
			unit_clauses.push_back(*it.begin());
	}
 
	for ( auto it : unit_clauses )
	{
		KB = updateKB( KB, it );
	}
 	
	for ( auto it : KB )
		if ( it.size() == 0 )
			return false;

	//line 247 to line 273 contains pure symbol heuristic
	map<vector<int>,set<int>>parity;
 
	for ( int i = 0; i<KB.size(); ++i )
	{
		for ( int j = 0; j<KB[i].size(); ++j )
		{
			vector<int>x(  KB[i][j].begin() + 1, KB[i][j].end()  );
			parity[ x ].insert(KB[i][j][0]);
		}
	}
 
	for ( auto it : parity )
	{
		if ( it.second.size() == 1 )
		{
			vector<int>temp_lit(4);
			temp_lit[0] = *it.second.begin();
			temp_lit[1] = it.first[0];
			temp_lit[2] = it.first[1];
			temp_lit[3] = it.first[2];
 
			KB = updateKB(KB,temp_lit);
 
			if ( KB.size() == 0 )
				return true;
		}
	}
 
	for ( auto it : KB )
		if ( it.size() == 0 )
			return false;
 
	vector<int>taking_lit = left.back();
	left.pop_back();
 	
 	//assume the literal in consideration to be false and check if formula is satisfiable
	taking_lit[0] = -1;
 
	bool ok1 = DPLL( updateKB(KB, taking_lit), left );
 
	if (ok1)
		return true;
 	
 	//assume the literal in consideration to be false and check if formula is satisfiable
	taking_lit[0] = 1;
 
	bool ok2 = DPLL( updateKB(KB, taking_lit), left );
 
	return (ok1 || ok2);
}
 
void intialiseKnowledgeBase(vector< clause >&knowledgeBase)
{
	for ( int i = 0; i<16; ++i )
	{
		for ( int j = i+1; j<16; ++j )
		{
			int r1 = i/4 + 1;
			int c1 = i%4 + 1;
 
			int r2 = j/4 + 1;
			int c2 = j%4 + 1;
 
			clause cl1,cl2;
			cl1.push_back({-1,'P',r1,c1});
			cl1.push_back({-1,'P',r2,c2});			
 
			cl2.push_back({-1,'W',r1,c1});
			cl2.push_back({-1,'W',r2,c2});			
			
			knowledgeBase.push_back(cl1);
			knowledgeBase.push_back(cl2);
		}		
	}
 
	for ( int i = 0; i<16; ++i )
	{
		int r = i/4 + 1;
		int c = i%4 + 1;
 
		clause c1,c2;
 
		c1.push_back({-1,'B',r,c});
		c2.push_back({-1,'S',r,c});
 
		for ( int j = 0; j<4; ++j )
		{
			int curr = r + dx[j];
			int curc = c + dy[j];
 
			if ( !valid(curr,curc) )
				continue;
 
			c1.push_back({1,'P',curr,curc});
			c2.push_back({1,'W',curr,curc});
		}
 
		assert(c1.size()>1);
		knowledgeBase.push_back(c1);
		knowledgeBase.push_back(c2);
	}	
 
	for ( int i = 0; i<16; ++i )
	{
		int r = i/4 + 1;
		int c = i%4 + 1;
 
		int cnt = 0;
		
		for ( int j = 0; j<4; ++j )
		{
			int curr = r + dx[j];
			int curc = c + dy[j];
 
			if ( !valid(curr,curc) )
				continue;
 
			clause c1,c2;
 
			c1.push_back({-1,'P',r,c});
			c2.push_back({-1,'W',r,c});
 
			c1.push_back({1,'B',curr,curc});
			c2.push_back({1,'S',curr,curc});
 
			knowledgeBase.push_back(c1);
			knowledgeBase.push_back(c2);
 
		}
 
	}
}
 
void AgentPrecept()
{
	breeze = false;
	stench = false;
 
	for ( int j = 0; j<4; ++j )
	{
		int rr = cur_x + dx[j];
		int cc = cur_y + dy[j];
 
		if ( !valid(rr,cc) )
			continue;
 
		stench|=( mat[rr][cc] == 'W' );
		breeze|=( mat[rr][cc] == 'P' ); 
	} 
 
	cout<<"Percept [";
 
	if ( breeze )
		cout<<"True, ";
	else
		cout<<"False, ";
 
	if ( stench )
		cout<<"True]";
	else
		cout<<"False]";
 
	cout<<"\n";
}
 
void AgentCurLoc()
{
	cout<<"Current Location: ["<<cur_x<<", "<<cur_y<<"]\n";
}

void initialise(vector<literal>&left, map< pair<int,int>, string>&act)
{

	for ( int i = 0; i<16; ++i )
	{
		int r1 = i/4 + 1;
		int c1 = i%4 + 1;
		left.push_back({0,'P',r1,c1});
		left.push_back({0,'W',r1,c1});
		left.push_back({0,'S',r1,c1});
		left.push_back({0,'B',r1,c1});
	}

 	act[{1,0}] = "RIGHT";
 	act[{-1,0}] = "LEFT";
 	act[{0,1}] = "DOWN";
 	act[{0,-1}] = "UP";


	for ( int i=1; i<=4; ++i )
		for ( int j = 1; j<=4; ++j )
			mat[i][j] = '.';

	cout<<"Please specify the coordinates of pit in a space spearated fashion, for example : if pit is in 2nd row from the top and 3rd column from left, type 3 2\n";
	int x,y;
	cin>>x>>y;
	mat[x][y] = 'P';

	cout<<"Please specify the coordinates of wumpus in a space spearated fashion, for example : if wumpus is in 2nd row from the top and 3rd column from left, type 3 2\n";
	cin>>x>>y;
	mat[x][y] = 'W';

}

signed main()
{
	vector<clause>knowledgeBase;
	//inReach will act as frontier set, it conatins those unexplored cells which we can reach by walking strictly on the cells which we have explored
	map< pair<int,int>, int>inReach;

 	map< pair<int,int>, string>act;

 	//contains all the possible literals in wumpus world model, total 64 literals 
	vector<literal>left;
 	
 	initialise(left,act);

 	//This will add all the sentences relating breeze to pit, stenct to wumpus, and the fact that there is exactly one pit and exactly one wumpus to the knowledge base
	intialiseKnowledgeBase(knowledgeBase);

	do
	{
		AgentCurLoc();

		reached[cur_x][cur_y] = 1;
		
		knowledgeBase =  updateKB(knowledgeBase,{-1,'P',cur_x,cur_y});
		knowledgeBase =  updateKB(knowledgeBase,{-1,'W',cur_x,cur_y});
 
		AgentPrecept();
 		
 		//if breeze is detected / undetected, then update knowledge base accordingly
		if ( breeze )
			knowledgeBase =  updateKB(knowledgeBase,{1,'B',cur_x,cur_y});
 
		else
			knowledgeBase =  updateKB(knowledgeBase,{-1,'B',cur_x,cur_y});

		//if stench is detected / undetected, then update knowledge base accordingly
		if ( stench )
			knowledgeBase =  updateKB(knowledgeBase,{1,'S',cur_x,cur_y});
 
		else
			knowledgeBase =  updateKB(knowledgeBase,{-1,'S',cur_x,cur_y});
 	
 		//add cells in frontier set i.e. inReach
		for ( int j = 0; j<4; ++j )
		{
			int nx = cur_x + dx[j];
			int ny = cur_y + dy[j];
 
			if ( !valid(nx,ny) )
				continue;
 
			if (!reached[nx][ny])
				inReach[{nx,ny}] = 1;
		}
 	
 		//find a cell in frontier set which is safe to visit, using DPLL algorithm 
		for ( auto it : inReach )
		{
			int t_x = it.first.first;
			int t_y = it.first.second;
 
			vector<clause>kb1 = updateKB(knowledgeBase,{1,'P',t_x,t_y});
			vector<clause>kb2 = updateKB(knowledgeBase,{1,'W',t_x,t_y});
			vector<clause>kb3 = updateKB(knowledgeBase,{-1,'P',t_x,t_y});
			vector<clause>kb4 = updateKB(kb3,{-1,'W',t_x,t_y});
 
			bool case1 = DPLL(kb1,left);
			bool case2 = DPLL(kb2,left);
			bool case3 = DPLL(kb4,left);
 
			if ( !case1 && !case2 && case3 )
			{
				inReach.erase(inReach.find(it.first));
				reached[t_x][t_y] = 1;
				vector< pair<int,int> >path = findPath(cur_x,cur_y,t_x,t_y);

				for ( int i = 1; i<path.size(); ++i )
				{
					cout<<"Action Taken: "<<act[{path[i].first-path[i-1].first,path[i].second-path[i-1].second}]<<", ";
					cur_x = path[i].first;
					cur_y = path[i].second;

					if (i!=path.size()-1)
						AgentCurLoc();					
				}

				cur_x = t_x;
				cur_y = t_y;
				break;
			}
		}
 
	}
	while(!reached[4][4]);

	cout<<"DPLL Algorithm was called "<<dpll_calls<<" times.\n";

	printclock;
}