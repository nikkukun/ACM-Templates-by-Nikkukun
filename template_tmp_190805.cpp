#include<bits/stdc++.h>
using namespace std;

typedef long long ll;
typedef unsigned int ui;
typedef unsigned long long ull;
typedef pair<int,int> pint;
typedef long double ld;
typedef __int128 i128;

/*
	Prime Table
	929292929
	299213
	19260817
	991145149
*/

const int N = 299213;
const int INF = 0x3f3f3f3f;
const ll INF_LL = 0x3f3f3f3f3f3f3f3f;
const int MOD = 929292929;

// =============== 图论 / Graph Theroy ===============

namespace _TwoSAT{
	// 两倍空间
	vector<int> a[N*2];
	stack<int> s; bool mark[N*2];
	
	// x==valX || y==valY
	void AddClause(int x,bool vx,int y,bool vy){
		x=x*2+vx, y=y*2+vy;
		a[x^1].push_back(y);
		a[y^1].push_back(x);
	}

	void Init(){
		for(int i=0;i<N*2;i++)
			a[i].clear();
		s=stack<int>();
		memset(mark,0,sizeof(mark));
	}

	bool DFS(int u){
		if(mark[u^1])return 0;
		if(mark[u])return 1;
		s.push(u); mark[u]=1;
		for(int i=0;i<a[u].size();i++)
			if(!DFS(a[u][i]))return 0;
		return 1;
	}

	// 下标从0开始
	bool Solve(int n){
		for(int i=0;i<n*2;i++)
			if(!mark[i]&&!mark[i^1])
				if(!DFS(i)){
					while(s.top()!=i)
						mark[s.top()]=0, s.pop();
					mark[i]=0, s.pop();
					if(!DFS(i^1))return 0;
				}
		return 1;
	}
};

// bitset 优化传递闭包
// REVIEW: https://www.luogu.org/problem/P4306
struct _TransitiveClosure{
	void Floyd(int n){
		bitset<N> f[N];
		for(int k=1; k<=n; k++)
			for(int i=1; i<=n; i++)
				if(f[i][k]) f[i] |= f[k];
	}
};

// REVIEW: https://www.luogu.org/problem/P4779
struct _Dijkstra{
	int dis[N];
	void Dijkstra(int st){
		memset(dis, 0x3f, sizeof dis);
		dis[st] = 0;
		priority_queue<pint, vector<pint>, greater<pint> > q;
		q.push(make_pair(0, st));

		static bool vst[N];
		while(!q.empty()){
			int u = q.top().second; q.pop();
			if(vst[u]) continue;
			vst[u] = 1;
			for(auto e: a[u]){
				int v = e.v, w = e.w;
				if(dis[v] > dis[u] + w){
					dis[v] = dis[u] + w;
					q.push(make_pair(dis[v], v));
				}
			}
		}
	}
};

// 邻接矩阵形式
// FIXME: 修改成邻接表形式
// 栈中是倒序的
// REVIEW: https://www.luogu.org/problem/P1431
struct EulerLoop{
	int g[N][N];
	int stk[N];

	void EulerLoop(int u){
		for(int v=1; v<N; v++){
			if(g[u][v] == 0) continue;
			g[u][v] = g[v][u] = 0;
			EulerLoop(v);
			stk[++stk[0]] = v;
		}
	}

	// 返回是否存在欧拉回路
	bool Solve(){
		int n; cin >> n;
		
		static int deg[N];
		for(int i=1; i<=n; i++){
			char u,v; cin >> u >> v;
			// 无向图，可以改成有向图
			g[u][v] = g[v][u] = 1;
			deg[u]++; deg[v]++;
		}

		int cnt1 = 0;
		for(int i=1; i<N; i++)
			cnt1 += deg[i]&1;
		if(cnt1==1 || cnt1>2) return 0;

		// 保证字典序最小
		for(int i=1; i<N; i++){
			if(deg[i] == 0) continue;
			if(cnt1 && deg[i]%2==0) continue;
			EulerLoop(i);
			stk[++stk[0]] = i;
			break;
		}
		// 可能不连通
		if(stk[0] != n+1) return 0;

		// stk 是欧拉回路上的点（起点出现两次）
		reverse(stk+1, stk+stk[0]+1);

		return 1;
	}
};

// REVIEW: https://www.luogu.org/problem/P2341
namespace StronglyConnectedComponent{
	vector<int> a[N];
	// sccId, sccSiz
	int sid[N], siz[N];

	int tms;
	int low[N], dfn[N], stk[N];

	// Tarjan 会遍历父边，不需要 continue 掉
	void Tarjan(int u){
		dfn[u] = low[u] = ++tms;
		stk[++stk[0]] = u;
		for(auto v: a[u]){
			if(!dfn[v]){
				Tarjan(v);
				low[u] = min(low[u], low[v]);
			}else if(!sid[v]){
				low[u] = min(low[u], dfn[v]);
			}
		}
		if(dfn[u] == low[u]){
			int id = ++sid[0];
			int &o = stk[0];
			while(stk[o] != u){
				sid[stk[o]] = id;
				o--; siz[id]++;
			}
			sid[stk[o]] = id; o--; siz[id]++;
		}
	}

	void Solve(){
		for(int i=1; i<=n; i++)
			if(!sid[i])
				Tarjan(i);
		// Process();
		// 连边时，连的是 (sid[u], sid[v])
	}
};

// =============== 网络流 / Network Flow ===============

namespace _MaxFlow{
	struct Dinic{
		struct Edge{
			int v, res;
		};
		vector<Edge> edg;
		vector<int> a[V];
		int st, ed;

		void Clear(){
			edg.clear();
			for(int i=0; i<V; i++)
				a[i].clear();
		}

		void AddEdge(int u, int v, int cap){
			edg.push_back((Edge){v, cap});
			edg.push_back((Edge){u, 0});
			int siz = edg.size();
			a[u].push_back(siz - 2);
			a[v].push_back(siz - 1);
		}

		int dep[V];
		bool BFS(){
			memset(dep, -1, sizeof(dep));
			dep[st] = 0;
			queue<int> q; q.push(st);

			while(!q.empty()){
				int u = q.front(); q.pop();
				for(auto i: a[u]){
					auto e = edg[i];
					if(dep[e.v] == -1 && e.res > 0){
						q.push(e.v);
						dep[e.v] = dep[u] + 1;
					}
				}
			}

			return dep[ed] != -1;
		}

		int cur[V];
		double DFS(int u, int minF){
			if(u == ed || minF == 0)
				return minF;

			int sumF = 0;
			// 传 cur 引用
			for(int &i=cur[u]; i<a[u].size(); i++){
				// 传 edg 引用
				auto &e = edg[a[u][i]];
				if(dep[e.v] == dep[u]+1){
					int tmpF = DFS(e.v, min(e.res, minF));
					if(tmpF <= 0) continue;
					e.res -= tmpF; edg[a[u][i]^1].res += tmpF;
					sumF += tmpF; minF -= tmpF;
				}
				if(minF == 0) break;
			}

			return sumF;
		}

		int MaxFlow(){
			int ret = 0;
			while(BFS()){
				memset(cur, 0, sizeof(cur));
				ret += DFS(st, INF);
			}
			return ret;
		}
	};
};

namespace _MaxFlowMinCost{
	struct Dinic{
		struct Edge{int v,w,res;};
		vector<Edge> edg;
		vector<int> a[N*2];
		int st,ed;

		void AddEdge(int u,int v,int w,int cap){
			edg.push_back((Edge){v,w,cap});
			edg.push_back((Edge){u,-w,0});
			int siz=edg.size();
			a[u].push_back(siz-2);
			a[v].push_back(siz-1);
		}

		int dis[N*2],pa[N*2],det[N*2];
		bool SPFA(){
			static int inQ[N*2];
			memset(inQ,0,sizeof(inQ));
			memset(dis,0x3f,sizeof(dis));
			deque<int> q;q.push_back(st);
			dis[st]=0, inQ[st]=1, det[st]=INF, pa[st]=-1;

			while(!q.empty()){
				int u=q.front();q.pop_front();inQ[u]=0;
				for(int i=0;i<a[u].size();i++){
					Edge &e=edg[a[u][i]];
					if(e.res>0 && dis[e.v]>dis[u]+e.w){
						dis[e.v]=dis[u]+e.w;
						det[e.v]=min(det[u],e.res);
						pa[e.v]=a[u][i];
						if(!inQ[e.v]){
							if(!q.empty() && dis[q.front()]>=dis[e.v])q.push_front(e.v);
							else q.push_back(e.v);
							inQ[e.v]=1;
						}
					}
				}
			}

			return dis[ed]!=INF;
		}

		void Augment(int &w){
			w+=dis[ed]*det[ed];
			int u=ed;
			while(u!=st){
				edg[pa[u]].res-=det[ed];
				edg[pa[u]^1].res+=det[ed];
				u=edg[pa[u]^1].v;
			}
		}

		int MaxFlowMinCost(){
			int ret=0;
			while(SPFA())Augment(ret);
			return ret;
		}
	};
};

namespace _Hungary{
	int g[N][N];
	bool vst[N]; int lnk[N];

	bool DFS(int u,int n){
		for(int v=1; v<=n; v++)
			if(g[u][v] && !vst[v]){
				vst[v] = 1;
				if(!lnk[v] || DFS(lnk[v], n)){
					lnk[v] = u;
					return 1;
				}
			}
		return 0;
	}

	int Match(int n){
		int ans = 0;
		for(int i=1; i<=n; i++){
			memset(vst, 0, sizeof(vst));
			if(DFS(i, n)) ans++;
		}
		return ans;
	}
};

// DEBUG:
namespace _MinVertexCover{
	int lnk[N];
	bool inS[N],inT[N];
	
	bool DFS(int u,int n){
		inS[u]=1;
		for(auto v:a[u]){
			if(inT[v])continue;
			inT[v]=1;
			if(!lnk[v]||DFS(lnk[v],n)){
				lnk[v]=u;
				return 1;
			}
		}
		return 0;
	}
	
	void Hungary(int n){
		static bool isMatch[N];
		for(int i=1;i<=n;i++){
			fill(inT+1,inT+n+1,0);
			if(DFS(i,n))isMatch[i]=1;
		}
	
		fill(inS+1,inS+n+1,0);
		fill(inT+1,inT+n+1,0);
	
		vector<int> ans;
		for(int i=1;i<=n;i++)
			if(!isMatch[i])DFS(i,n);
		for(int i=1;i<=n;i++)
			if(__builtin_parity(b[i])==1 && inS[i])
				ans.push_back(b[i]);
		for(int i=1;i<=n;i++)
			if(__builtin_parity(b[i])==0 && !inT[i])
				ans.push_back(b[i]);
		
		cout<<ans.size()<<endl;
		for(auto i:ans)
			cout<<i<<' ';
	}
};

namespace _KM{
	int g[N][N];

	int lx[N],ly[N],lnk[N],slack[N];
	bool inS[N],inT[N];

	bool DFS(int u,int n){
		inS[u]=1;
		for(int v=1;v<=n;v++){
			if(inT[v])continue;
			int w=lx[u]+ly[v]-g[u][v];
			if(w==0){
				inT[v]=1;
				if(!lnk[v] || DFS(lnk[v],n)){
					lnk[v]=u;
					return 1;
				}
			}else slack[v]=min(slack[v],w);
		}
		return 0;
	}

	void Update(int n){
		int det=INF;
		for(int i=1;i<=n;i++)
			if(!inT[i])
				det=min(det,slack[i]);
		for(int i=1;i<=n;i++){
			if(inS[i])lx[i]-=det;
			if(inT[i])ly[i]+=det;
			else slack[i]-=det;
		}
	}

	// n是两侧点的最大值，从1标号
	void KM(int n){
		for(int i=1;i<=n;i++){
			lx[i]=-INF;
			for(int j=1;j<=n;j++)
				lx[i]=max(lx[i],g[i][j]);
		}
		for(int i=1;i<=n;i++){
			memset(slack,0x3f,sizeof(slack));
			while(1){
				memset(inS,0,sizeof(inS));
				memset(inT,0,sizeof(inT));
				if(DFS(i,n))break;
				else Update(n);
			}
		}
	}
};

// =============== 字符串 / String Algorithm ===============

// FIXME: 修改成不用string的版本
namespace _KMP{
	int Init(int f[],string s){
		f[0]=f[1]=0;
		for(int i=1;i<s.length();i++) {
			int j=f[i];
			while(j&&s[i]!=s[j])j=f[j];
			f[i+1] = (s[i]==s[j])?j+1:0;
		}
	}
	int Query(string s,string t,int f[]){
		int cnt=0,j=0;
		for(int i=0;i<s.length();i++){
			while(j&&s[i]!=t[j])j=f[j];
			if(s[i]==t[j])j++;
			if(j==t.length())cnt++;
		}
		return cnt;
	}
};

struct AhoCorasick{
	int ch[M][C], f[M], pre[M];
	int isEnd[M];
	int idx;

	void Init(){
		memset(ch, 0, sizeof(ch));
		memset(f, 0, sizeof(f));
		memset(pre, 0, sizeof(pre));
		memset(isEnd, 0, sizeof(isEnd));
		idx = 0;
	}

	// [1, n]
	void Build(char s[], int n, int id){
		int o = 0;
		for(int i=1; i<=n; i++){
			// 注意加入的是 [0, 26)
			int c = s[i]-'a';
			if(ch[o][c]) o = ch[o][c];
			else o = ch[o][c] = ++idx;
		}
		isEnd[o] = id;
	}

	void GetFail(){
		queue<int> q;
		for(int c=0; c<C; c++)
			if(ch[0][c]) q.push(ch[0][c]);

		while(!q.empty()){
			int o = q.front(); q.pop();
			for(int c=0; c<C; c++){
				int &u = ch[o][c];
				int j = f[o];
				if(!u){
					u = ch[j][c];
					continue;
				}
				q.push(u);
				while(j && !ch[j][c]) j = f[j];
				f[u] = ch[j][c];
				pre[u] = isEnd[f[u]] ? f[u] : pre[f[u]];
			}
		}
	}
	
	// [1, n]
	void GetMatchPos(char s[], int n, vector<int> pos[], int _len[]){
		int o = 0;
		for(int i=1; i<=n; i++){
			// 根据上面的构造，理论上不用跳 fail
			while(o && ch[o][s[i]-'a'] == 0)
				o = f[o];
			o = ch[o][s[i]-'a'];
			int p = o;
			// 即使不是接受态，往前跳几下就可能是接受态了
			if(!isEnd[o] && pre[o]) p = pre[o];
			while(isEnd[p]){
				int id = isEnd[p];
				int len = _len[id];
				pos[len].push_back(i - len + 1);
				p = pre[p];
			}
		}
	}
};

// FIXME: 没用过，需要看看会不会出锅
namespace _Manacher{
	ll Manacher(char t[],int n){
		static char s[2*N]; 
		static int cnt[2*N],f[2*N];
		
		for(int i=0;i<=n*2;i++)
			cnt[i]=f[i]=0;
		
		for(int i=1;i<=n;i++){
			s[i*2-1]=t[i-1];
			s[i*2]=1;
		}
		s[0]=2,s[n*2]=3;

		int cur=f[0]=0,idx=0;
		for(int i=1;i<2*n;i++){
			int& j=f[i]; j=0;
			if(cur-i>=0&&2*idx-i>=0)j=min(f[2*idx-i],cur-i);
			while(s[i-j-1]==s[i+j+1])j++;
			if(i+j>cur)cur=i+j,idx=i;
			//ans=max(ans,(j*2+1)/2);
			
			cnt[max(0,i-j)]++;
			cnt[i+1]--;
		}

		ll ret=0;
		for(int i=1;i<=2*n;i++){
			cnt[i]+=cnt[i-1];
			if(i&1)ret+=cnt[i];
		}
		
		return ret;
	}
};

// SAM空间开两倍
namespace _SAM{
    int ch[N*2][C],pa[N*2],len[N*2],siz[N*2];
    int idx=1,pre=1;

    void Insert(int x){
        int p=pre,np=++idx;pre=np;
        siz[np]=1; len[np]=len[p]+1;
        for(;p&&ch[p][x]==0;p=pa[p])ch[p][x]=np;

        if(p==0)pa[np]=1;
        else{
            int q=ch[p][x];
            if(len[q]==len[p]+1)pa[np]=q;
            else{
                int nq=++idx; len[nq]=len[p]+1;
                memcpy(ch[nq],ch[q],sizeof(ch[q]));
                pa[nq]=pa[q]; pa[q]=pa[np]=nq;
                for(;p&&ch[p][x]==q;p=pa[p])ch[p][x]=nq;
            }
        }
    }

	// 本质不同子串个数 = sum_[i=1..n] len[i]-len[pa[i]]
	// PAM的pa只可能在前面，所以不需要拓扑
	// SAM里len越小越接近根节点，但是idx会越大，所以要拓扑一下
    int tmp[N*2],topo[N*2];
    void Build(){
    	for(int i=1;i<=idx;i++)tmp[len[i]]++;
    	for(int i=1;i<=idx;i++)tmp[i]+=tmp[i-1];
    	for(int i=1;i<=idx;i++)topo[tmp[len[i]]--]=i;
        for(int i=idx;i>1;i--){
            int v=topo[i], u=pa[v];
            siz[u]+=siz[v];
        }
	}

	int Init(char s[],int n){
		for(int i=1;i<=n;i++)
			_SAM::Insert(s[i]);
		_SAM::Build();
	}
};

namespace _PAM{
    int ch[N][C],pa[N]={1},len[N]={0,-1},siz[N];
    int idx=1,pre=0;

    void Insert(char s[],int pos){
        int p=pre, x=s[pos]-'a';
        for(;s[pos-len[p]-1]!=s[pos];)p=pa[p];
        if(ch[p][x]==0){
            int q=pa[p], np=++idx;
            len[np]=len[p]+2;
            for(;s[pos-len[q]-1]!=s[pos];)q=pa[q];
            pa[np]=ch[q][x]; ch[p][x]=np;
        }
        pre=ch[p][x]; siz[pre]++;
    }

	// 一个节点就是一个本质不同的回文串
	// 本质不同回文子串个数 = idx-1（去除两个根节点）
    ll Build(){
        ll ans=0;
        for(int i=idx;i>1;i--){
            siz[pa[i]]+=siz[i];
            ans=max(ans,1LL*siz[i]*len[i]);
        }
        return ans;
    }

	// 从1开始编号，默认s范围为[a,z]
	int Init(char s[],int n){
		for(int i=1;i<=n;i++)
			_PAM::Insert(s,i);
		printf("%lld",_PAM::Build());
	}
};

// DEBUG:
namespace SA{
	//a \in [0,n)
	//$a_n$ = min(0)
	//1 \leq a_i< m
	struct SuffixArray{
		int sa[N],hei[N],rnk[N];

		void Init(int *a,int n){
			InitSa(a,n);
			InitHeight(a,n);
			for(int i=0;i<n;i++){
				sa[i]=sa[i+1];
				hei[i]=hei[i+1];
				rnk[i]--;
			}
		}

		inline bool Cmp(int *a,int x,int y,int l){
			return a[x]==a[y]&&a[x+l]==a[y+l];
		}

		void InitSa(int *a,int n){
			int m=26;
			static int tmpX[N],tmpY[N],s[N];
			int *x=tmpX,*y=tmpY;

			a[n]=0;
			for(int i=0;i<m;i++)s[i]=0;
			for(int i=0;i<=n;i++)s[x[i]=a[i]]++;
			for(int i=1;i<m;i++)s[i]+=s[i-1];
			for(int i=n;i>=0;i--)sa[--s[x[i]]]=i;

			for(int i=1,p=1;p<=n;i<<=1,m=p){
				p=0;
				for(int j=n-i+1;j<=n;j++)y[p++]=j;
				for(int j=0;j<=n;j++)if(sa[j]>=i)y[p++]=sa[j]-i;
				for(int j=0;j<m;j++)s[j]=0;
				for(int j=0;j<=n;j++)s[x[y[j]]]++;
				for(int j=1;j<m;j++)s[j]+=s[j-1];
				for(int j=n;j>=0;j--)sa[--s[x[y[j]]]]=y[j];
				swap(x,y);
				p=1,x[sa[0]]=0;
				for(int j=1;j<=n;j++)x[sa[j]]=Cmp(y,sa[j-1],sa[j],i)?p-1:p++;
			}
		}

		void InitHeight(int *a,int n){
			for(int i=1;i<=n;i++)rnk[sa[i]]=i;
			for(int i=0,j,k=0;i<n;hei[rnk[i++]]=k)
				for(k?k--:0,j=sa[rnk[i]-1];a[i+k]==a[j+k];k++);
		}
	};
};

// =============== FFT / Fast Fourier Transformation ===============

struct Complex{
	double x,y;
	Complex(double _x=0,double _y=0){
		x=_x; y=_y;
	}
	Complex operator + (Complex a){
		return Complex(x+a.x,y+a.y);
	}
	Complex operator - (Complex a){
		return Complex(x-a.x,y-a.y);
	}
	Complex operator * (Complex a){
		return Complex(x*a.x-y*a.y,y*a.x+x*a.y);
	}
	Complex operator ~ (){
		return Complex(x,-y);
	}
};

namespace _FFT{
	// M需要开到比N大的2^n的两倍
	const int M=(1<<(__lg(N-1)+1))*2+5;
	const double PI=acos(-1.0);

	Complex rot[M];

	void FFT(Complex w[],int n,int op){
		static int r[M];
		for(int i=0;i<n;i++)
			r[i]=(r[i>>1]>>1)|((i&1)?n>>1:0);
		for(int i=0;i<n;i++)
			if(i<r[i])swap(w[i],w[r[i]]);
			
		for(int len=2;len<=n;len<<=1){
			int sub=len>>1;
			for(int l=0;l<n;l+=len){
				for(int i=l;i<l+sub;i++){
					Complex &r=rot[sub+i-l];
					Complex x=w[i];
					Complex y=(Complex){r.x,op*r.y}*w[i+sub];
					w[i]=x+y; w[i+sub]=x-y;
				}
			}
		}
	}

	// 无共轭优化
	// n是最高次项次数而不是长度
	// FIXME: 修改成长度而不是最高次项
	// TODO: 测试能不能正常运行
	void Cal(int f[],int g[],int n,int ans[]){
		static Complex a[N],b[N];

		int len=1;
		for(;len<=(n<<1);len<<=1);
		for(int i=0;i<len;i++)
			a[i].x=f[i], b[i].x=g[i];

		for(int i=1;i<len;i<<=1)
			for(int j=0;j<i;j++)
				rot[i+j]=Complex(cos(PI*j/i),sin(PI*j/i));

		FFT(a,len,1); FFT(b,len,1);
		for(int i=0;i<len;i++)
			a[i]=a[i]*b[i];
		FFT(a,len,-1);

		for(int i=0;i<len;i++)
			ans[i]=round(a[i].x/len);
	}

	// 有共轭优化
	// n是最高次项次数而不是长度
	// FIXME: 修改成长度而不是最高次项
	// TODO: 测试能不能正常运行
	void Cal_Conj(int f[],int g[],int n,int ans[]){
		static Complex a[N];

		int len=1;
		for(;len<=(n<<1);len<<=1);
		for(int i=0;i<len;i++)
			a[i].x=f[i], a[i].y=g[i];

		for(int i=1;i<len;i<<=1)
			for(int j=0;j<i;j++)
				rot[i+j]=Complex(cos(PI*j/i),sin(PI*j/i));

		FFT(a,len,1);
		for(int i=0;i<len;i++)
			a[i]=a[i]*a[i];
		FFT(a,len,-1);

		for(int i=0;i<len;i++)
			ans[i]=round(a[i].y/2/len);
	}
};

// FIXME: 没有预处理rot
// NOTE: 中途可能会变成负数，最后需要模一下
namespace _NTT{
	const int MOD = 998244353, G = 3;

	ll QPow(ll bas, int t);
	ll Inv(ll x);

	void NTT(int w[], int n, int op){
		static int r[N];

		for(int i=0; i<n; i++)
			r[i] = (r[i>>1] >> 1) | ((i&1) ? n>>1 : 0);
		for(int i=0; i<n; i++)
			if(i < r[i]) swap(w[i], w[r[i]]);
			
		for(int len=2; len<=n; len<<=1){
			int sub = len>>1;
			ll det = QPow(3, MOD-1 + op * (MOD-1) / len);
			for(int l=0; l<n; l+=len){
				ll rot = 1;
				for(int i=l; i<l+sub; i++){
					ll x = w[i];
					ll y = rot * w[i+sub] % MOD;
					w[i] = (x + y) % MOD;
					w[i+sub] = (x - y) % MOD;		// maybe minus
					rot = rot * det % MOD;
				}
			}
		}
		
		if(op == 1) return;
		ll inv = Inv(n);
		for(int i=0; i<n; i++)
			w[i] = inv * w[i] % MOD;
	}
};

// 7次FFT
namespace _MTT_7{
	using namespace _FFT;
	
	void MTT(int f[],int g[],int n,int ans[]){
		static const int D=(1<<15);
		static const int MOD=998244353;
		static Complex a[M],b[M],c[M],d[M];

		memset(a,0,sizeof(a)); memset(b,0,sizeof(b));
		memset(c,0,sizeof(c)); memset(d,0,sizeof(d));

		int len=1;
		for(;len<=(n<<1);len<<=1);

		for(int i=0;i<=n;i++){
			a[i].x=f[i]/D; b[i].x=f[i]%D;
			c[i].x=g[i]/D; d[i].x=g[i]%D;
		}

		for(int i=1;i<len;i<<=1)
			for(int j=0;j<i;j++)
				rot[i+j]=Complex(cos(PI*j/i),sin(PI*j/i));

		FFT(a,len,1); FFT(b,len,1);
		FFT(c,len,1); FFT(d,len,1);

		for(int i=0;i<len;i++){
			Complex _a=a[i], _b=b[i], _c=c[i], _d=d[i];
			a[i]=_a*_c;
			b[i]=_a*_d+_b*_c;
			c[i]=_b*_d;
		}

		FFT(a,len,-1); FFT(b,len,-1); FFT(c,len,-1);

		for(int i=0;i<len;i++){
			ll w=0;
			w += (ll)round(a[i].x/len)%MOD*D%MOD*D%MOD;
			w += (ll)round(b[i].x/len)%MOD*D%MOD;
			w += (ll)round(c[i].x/len)%MOD;
			ans[i]=w%MOD;
		}
	}
};

// 4次FFT
namespace _MTT_4{
	using namespace _FFT;

	void MTT(int f[],int g[],int n,int ans[]){
		static const int D=(1<<15);
		static const int MOD=998244353;
		static Complex a[M],b[M],c[M],d[M];

		int len=1;
		for(;len<=(n<<1);len<<=1);
		for(int i=0;i<len;i++)
			a[i]=b[i]=Complex(0,0);

		for(int i=0;i<=n;i++){
			a[i].x=f[i]/D; a[i].y=f[i]%D;
			b[i].x=g[i]/D; b[i].y=g[i]%D;
		}

		for(int i=1;i<len;i<<=1)
			for(int j=0;j<i;j++)
				rot[i+j]=Complex(cos(PI*j/i),sin(PI*j/i));

		FFT(a,len,1); FFT(b,len,1);

		for(int i=0;i<len;i++){
			Complex t,a0,a1,b0,b1;

			t = ~a[(len-i)%len];
			a0 = (a[i]-t)*Complex(0,-0.5);
			a1 = (a[i]+t)*Complex(0.5,0);
			t = ~b[(len-i)%len];
			b0 = (b[i]-t)*Complex(0,-0.5);
			b1 = (b[i]+t)*Complex(0.5,0);
			
			c[i] = a1*b1;
			d[i] = a1*b0+a0*b1+a0*b0*Complex(0,1);
		}

		FFT(c,len,-1); FFT(d,len,-1);

		// 这里应该是 <= n
		for(int i=0;i<n;i++){
			ll w = 0;
			w += ll(round(c[i].x/len))%MOD*D*D;
			w += ll(round(d[i].x/len))%MOD*D;
			w += ll(round(d[i].y/len))%MOD;
			ans[i] = w%MOD;
		}
	}
};


// DEBUG:
namespace FWT{
	// n 是个 2^p 的数，也就是多项式的阶数
	// 但是最高项是 x^(n-1)
	// 可能需要取模

	void FWT_OR(int w[], int n, int op){
		for(int len=1; len<n; len<<=1)
			for(int i=0; i<n; i+=len*2)
				for(int j=0; j<len; j++)
					w[i+j+len] += w[i+j]*op;
	}

	void FWT_AND(int w[], int n, int op){
		for(int len=1; len<n; len<<=1)
			for(int i=0; i<n; i+=len*2)
				for(int j=0; j<len; j++)
					w[i+j] += w[i+j+len]*op;
	}

	// 如果 w 是 ull，则应该在最后再除 n 
	// 因为运算过程不保证逆存在
	// 事实上我觉得只要 w 不是 double，都需要最后除
	// x+y x-y 是奇数什么的非常有可能吧…
	const int INV2 = 929292929;
	void FWT_XOR(int w[], int n, int op){
		for(int l=1; l<n; l<<=1)
			for(int i=0; i<n; i+=l*2)
				for(int j=0; j<l; j++){
					int x = w[i+j], y = w[i+j+l];
					w[i+j] = x+y;
					w[i+j+l] = x-y;
				}
		if(op == 1) return;
		for(int i=0; i<n; i++) w[i] /= n;
		// for(int i=0; i<n; i++) w[i] *= Inv(n);
	}
};

// =============== 多项式 / Polynomial ===============

namespace _PolyInv{
	const int MOD=998244353;
	ll Inv(ll x);

	// MTT版本
	using namespace _MTT_4;
	void PolyInv(int a[],int b[],int n){
		if(n==1){
			b[0]=Inv(a[0]);
			return;
		}
		PolyInv(a,b,(n+1)/2);
		
		static int c[N];
		for(int i=0;i<n;i++)c[i]=0;

		MTT(a,b,n,c);
		for(int i=0;i<n;i++)c[i]=MOD-c[i];
		c[0]=(2+c[0])%MOD;
		MTT(c,b,n,b);
	}

	// NTT版本
	using namespace _NTT;
	void PolyInv_NTT(int a[],int b[],int n){
		if(n==1){
			b[0]=Inv(a[0]);
			return;
		}
		PolyInv(a,b,(n+1)/2);
		
		int len=1;
		for(;len<(n<<1);len<<=1);
		
		static int c[N];
		for(int i=0;i<n;i++)c[i]=a[i];
		for(int i=n;i<len;i++)c[i]=0;
		
		NTT(b,len,1); NTT(c,len,1);
		for(int i=0;i<len;i++)
			b[i]=(2LL-1LL*c[i]*b[i])%MOD*b[i]%MOD;
		NTT(b,len,-1);
		for(int i=n;i<len;i++)b[i]=0;
	}
};

namespace _PolyDiv{
	using namespace _PolyInv;
	const int MOD=998244353;

	// a = b*d + mod
	// FIXME: 改写成MTT形式

	// NTT版本
	using namespace _NTT;
	void PolyDiv(int a[],int b[],int n,int m,int d[],int mod[]){
		reverse(a,a+n+1); reverse(b,b+m+1);
		static int inv_b[N];
		PolyInv(b,inv_b,n-m+1);
		
		int len=1;
		for(;len<(n<<1);len<<=1);
		for(int i=0;i<=n;i++)d[i]=a[i];
		NTT(d,len,1); NTT(inv_b,len,1);
		for(int i=0;i<len;i++)
			d[i]=1LL*d[i]*inv_b[i]%MOD;
		NTT(d,len,-1);
		for(int i=n-m+1;i<len;i++)
			d[i]=0;

		reverse(a,a+n+1); reverse(b,b+m+1);
		reverse(d,d+n-m+1);
		
		static int _b[N],_d[N];
		for(int i=0;i<=m;i++)_b[i]=b[i];
		for(int i=0;i<=n-m;i++)_d[i]=d[i];
		NTT(_b,len,1); NTT(_d,len,1);
		for(int i=0;i<len;i++)
			mod[i]=1LL*_b[i]*_d[i]%MOD;
		NTT(mod,len,-1);

		for(int i=0;i<m;i++)
			mod[i]=(a[i]-mod[i]+MOD)%MOD;
	}
};

// =============== 树 / Tree Algorithm ===============

// DEBUG:
namespace HeavyLightDecomposition{
	SegTree t;
	int dep[N],siz[N],pa[N],son[N],top[N],idx[N];
	int nIdx;

	void Build(){
		nIdx=dep[0]=siz[0]=son[0]=0;
		DFS1(); DFS2();
	}
	void DFS1(int u=1,int pa=0){
		dep[u]=dep[HLDcp::pa[u]=pa]+1;
		siz[u]=1;son[u]=0;
		for(int i=0;i<a[u].size();i++){
			int v=a[u][i];
			if(v==pa)continue;
			DFS1(v,u);
			if(siz[v]>siz[son[u]])son[u]=v;
			siz[u]+=siz[v];
		}
	}
	void DFS2(int u=1,int pa=0){
		idx[u]=++nIdx;top[u]=u;
		if(son[pa]==u)top[u]=top[pa];
		if(son[u])DFS2(son[u],u);
		for(int i=0;i<a[u].size();i++){
			int v=a[u][i];
			if(v==pa||v==son[u])continue;
			DFS2(v,u);
		}
	}
	void Add(int u){
		while(top[u]!=0){
			t.Update(idx[top[u]],idx[u],1);
			u=pa[top[u]];
		}
	}
	void Delete(int u){
		t.Update(idx[u],idx[u]+siz[u]-1,0);
	}
	// 对边操作，每个点代表(u,pa[u])这条边
	void Modify(int u,int v,int w){
		while(top[u]!=top[v]){
			if(dep[top[u]]<dep[top[v]])swap(u,v);
			t.Modify(idx[top[u]],idx[u],1,w,1,nIdx);
			u=pa[top[u]];
		}
		// 节点相同则退出
		if(u==v)return;
		if(dep[u]>dep[v])swap(u,v);
		t.Modify(idx[u]+1,idx[v],1,w,1,nIdx);
	}
};

// DEBUG:
// FIXME: 没有建树过程
namespace FHQTreap{
	struct Node{
		int v,w,siz,lazy; ll sum;
		Node *lch,*rch;

		Node(int _v=0){
			v=_v, w=rand(), siz=1;
			sum=v, lazy=0;
			lch=rch=nullptr;
		}
		void Maintain(){
			siz=1; sum=v;
			if(lch!=nullptr)
				siz+=lch->siz,sum+=lch->sum;
			if(rch!=nullptr)
				siz+=rch->siz,sum+=rch->sum;
		}
		void Pushdown(){
			if((this==nullptr)||lazy==0)return;
			if(lch!=nullptr)lch->lazy^=1;
			if(rch!=nullptr)rch->lazy^=1;
			swap(lch,rch); lazy=0;
		}
	};

	typedef pair<Node*,Node*> pNode;
	Node mp[N];

	struct Treap{
		Node *rt,*pit;

		Treap(){
			pit=mp; rt=nullptr;
		}
		Node* NewNode(int v){
			*pit=Node(v);
			return pit++;
		}
		void Insert(int v){
			Node* o=NewNode(v);
			rt=Merge(rt,o);
		}
		pNode Split(Node* o,int k){
			pNode ret(nullptr,nullptr);
			if(o==nullptr)return ret;

			o->Pushdown();
			int siz=(o->lch==nullptr)?0:o->lch->siz;
		
			if(k<=siz){
				ret=Split(o->lch,k);
				o->lch=ret.second;
				o->Maintain();
				ret.second=o;
			}else{
				ret=Split(o->rch,k-siz-1);
				o->rch=ret.first;
				o->Maintain();
				ret.first=o;
			}

			return ret;
		}
		Node* Merge(Node* a,Node* b){
			if(a==nullptr)return b;
			if(b==nullptr)return a;

			a->Pushdown(); b->Pushdown();
			if(a->w < b->w){
				a->rch=Merge(a->rch,b);
				a->Maintain();
				return a;
			}else{
				b->lch=Merge(a,b->lch);
				b->Maintain();
				return b;
			}
		}
		void Print(Node* o){
			if(o==nullptr)return;
			o->Pushdown();
			Print(o->lch);
			printf("%d ",o->v);
			Print(o->rch);
		}
		ll Inverse(int L,int R){
			pNode a=Split(rt,L-1);
			pNode b=Split(a.second,R-L+1);
			b.first->lazy^=1;		//b一定非空
			int ret=b.first->sum;
			rt=Merge(Merge(a.first,b.first),b.second);
			return ret;
		}
	};
};

// DEBUG:
namespace _DFS4Root{
	int _maxSiz;
	int maxSiz[N];
	void DFS(int u,int pa,int n){
		static int siz[N]; siz[u]=1;
		for(auto v:a[u]){
			if(v==pa)continue;
			DFS(v,u,n);
			siz[u]+=siz[v];
			maxSiz[u]=max(maxSiz[u],siz[v]);
		}
		maxSiz[u]=max(maxSiz[u],n-siz[u]);
		_maxSiz=min(_maxSiz,maxSiz[u]);
	}
};

// DEBUG:
namespace _TreeHash{
	const int P=99299299;
	// f[u] = xor f[v]*P+siz[v]
	ull TreeHash(int u,int pa){
		static int siz[N];
		siz[u]=1; ull ret=0;
		for(auto v:a[u]){
			if(v==pa)continue;
			auto _hash=TreeHash(v,u);
			ret^=_hash*P+siz[v];
			siz[u]+=siz[v];
		}
		return ret;
	}
};

// DEBUG:
namespace DSUOnTree{
	int ans[N],cnt[N],sum[N];

	void Modify(int u,int pa,int op,int son){
		if(op==1)sum[++cnt[c[u]]]++;
		else sum[cnt[c[u]]--]--;
		for(auto v:a[u])
			if(v!=pa && v!=son)
				Modify(v,u,op,son);
	}

	void DFS(int u,int pa,bool keep){
		int son=0;
		for(auto v:a[u])
			if(v!=pa && siz[v]>siz[son])
				son=v;
		for(auto v:a[u])
			if(v!=pa && v!=son)
				DFS(v,u,0);
		if(son)DFS(son,u,1);
		Modify(u,pa,1,son);

		for(auto p:qry[u])
			ans[p.first]=sum[p.second];

		if(!keep)Modify(u,pa,-1,0);
	}
};

// DEBUG:
namespace DCOnTree{
	bool vst[N];
	int rt;
	int siz[N],maxSiz[N]; 

	void DFS4Rt(int u,int pa,int sum){
		siz[u]=1;
		for(auto v:a[u])
			if(v!=pa && !vst[v]){
				DFS4Rt(v,u,sum);
				siz[u]+=siz[v];
			}
		maxSiz[u]=max(siz[u],sum-siz[u]);
		if(maxSiz[u]>maxSiz[rt])rt=u;
	}

	void DFS(int u,int pa,int dep,ll w1,ll w2){
		for(auto v:a[u])
			if(v!=pa && !vst[v])
				DFS(v,u,dep+1,w1,w2);
	}

	int in0[N],in1[N],out0[N],out1[N];

	// 计算经过该点路径的贡献
	void Cal(int u){
		for(auto v:a[u]){
			if(vst[v])continue;
			DFS(v,u,1,w[u],0);		//remove w[u] in path w2
		}
	}

	void Solve(int u){
		vst[u]=1; Cal(u);
		for(auto v:a[u]){
			if(vst[v])continue;
			DFS4Rt(v,rt=0,siz[v]);		//init rt=0
			Solve(v);
		}
	}

	int main(){
		DFS4Rt(1,rt=0,n);
		Solve(rt);
	}
};

// =============== 数论 / Number Theory ===============

// REVIEW: https://www.luogu.org/problem/P3383
// DEBUG:
namespace MillerRabin{
	bool MR(ll p){
		if(p==2)return 1;
		if(p<=1 || !(p&1))return 0;
		if(p==2152302898747LL)return 0;
		if(p==3215031751)return 0;

		mt19937_64 rng(time(0));
		for(int i=0;i<UPP;i++){
			ll a=rng()%(p-2)+2;
			for(ll k=p-1; !(k&1); k>>=1){
				ll t=QPow(a,k,p);
				if(t!=1 && t!=p-1)return 0;
				if(t==p-1)break;
			}
		}
		return 1;
	}
};

// DEBUG:
namespace PollardRho{
	ll QMul(i128 a,i128 b,ll mod){
		return a*b%mod;
	}

	inline ll Abs(ll x){
		return x>0?x:-x;
	}

	ll PR(ll x){
		if(MR(x))return x;

		mt19937_64 rng(time(0));
		ll t1=rng()%(x-1)+1;
		ll b=rng()%(x-1)+1;
		ll t2=(QMul(t1,t1,x)+b)%x;

		int cnt=0; ll p=1;
		while(t1!=t2){
			cnt++;
			p=QMul(p,Abs(t2-t1),x);
			if(p==0){
				ll g=__gcd(Abs(t2-t1),x);
				return max(PR(g),PR(x/g));
			}
			if(cnt==127){
				ll g=__gcd(p,x);
				if(g!=1 && g!=x)
					return max(PR(g),PR(x/g));
				cnt=0; p=1;
			}
			t1=(QMul(t1,t1,x)+b)%x;
			t2=(QMul(t2,t2,x)+b)%x;
			t2=(QMul(t2,t2,x)+b)%x;
		}

		ll g=__gcd(p,x);
		if(g!=1 && g!=x)
			return max(PR(g),PR(x/g));

		return 0;
	}

	// 找到最大质因子
	// 先MR判定再PR
	ll Cal(ll x){
		if(MR(x))cout<<"Prime\n";
		else if(x==1)cout<<"1\n";
		else{
			ll ans=0;
			while(ans==0)
				ans=PR(x);
			cout<<ans<<endl;
		}
	}
};

// Cal(a, b, c, n) = sum[i=1->n]: floor((a*i+b)/c)
// O(\log n)
namespace Euclidean{
	ll Cal(ll a, ll b, ll c, ll n){
		if(a == 0) return b/c*(n+1)%MOD;
		if(a>=c || b>=c)
			return (n*(n+1)/2%MOD*(a/c)%MOD + (n+1)*(b/c)%MOD + Cal(a%c, b%c, c, n)) %MOD;
		ll m = (a*n+b)/c;
		return (n*m%MOD - Cal(c, c-b-1, a, m-1))%MOD;
	}
};

// =============== 筛法 / Sieve Algorithm ===============

namespace LinearSieve{
	bool notPri[N]; int pri[N];
	int phi[N];
	
	void Phi(){
		phi[1] = 1;
		for(int i=2; i<N; i++){
			if(!notPri[i]){
				pri[++pri[0]] = i;
				phi[i] = i-1;
			}
			for(int j=1; j<=pri[0]; j++){
				int p = pri[j];
				if(i*p >= N) break;
				notPri[i*p] = 1;
				if(i % p){
					phi[i*p] = phi[i] * phi[p];
				}else{
					phi[i*p] = p * phi[i];
					break;
				}
			}
		}
	}
};

// DEBUG:
namespace DuSieve{
	const int N=3e6+5;
	bool notPri[N];
	int pri[N],mu[N],phi[N];
	ll sumMu[N],sumPhi[N];

	void Init(){
		mu[1]=1; phi[1]=1;
		for(int i=2;i<N;i++){
			if(!notPri[i]){
				pri[++pri[0]]=i;
				phi[i]=i-1;
				mu[i]=-1;
			}
			for(int j=1;j<=pri[0] && i*pri[j]<N;j++){
				int x=i*pri[j]; notPri[x]=1;
				if(i%pri[j]){
					mu[x]=-mu[i];
					phi[x]=phi[i]*(pri[j]-1);
				}else{
					mu[x]=0;
					phi[x]=phi[i]*pri[j];
					break;
				}
			}
		}

		for(int i=1;i<N;i++){
			sumMu[i]=sumMu[i-1]+mu[i];
			sumPhi[i]+=sumPhi[i-1]+phi[i];
		}
	}

	unordered_map<int,ll> _sumMu,_sumPhi;

	ll Mu(int n){
		if(n<N)return sumMu[n];
		if(_sumMu.count(n))return _sumMu[n];
		ll ret=1;
		// 实际上i和j可能爆int
		for(int i=2,j;i<=n;i=j+1){
			j=n/(n/i);
			ret-=Mu(n/i)*(j-i+1);
		}
		return _sumMu[n]=ret;
	}

	// 实际上ans可能爆ll
	ll Phi(int n){
		if(n<N)return sumPhi[n];
		if(_sumPhi.count(n))return _sumPhi[n];
		ll ret=1LL*(1+n)*n/2;
		// 实际上i和j可能爆int
		for(int i=2,j;i<=n;i=j+1){
			j=n/(n/i);
			ret-=Phi(n/i)*(j-i+1);
		}
		return _sumPhi[n]=ret;
	}
};

// =============== 离散数学 / Discrete Maths ===============

// REVIEW: https://ac.nowcoder.com/acm/contest/889/B
namespace QuadraticResidue{
	ll QPow(ll bas, int t);
	ll Inv(ll x);

	// _w 是新数域的虚部单位
	ll _w;
	struct Complex{
		ll x, y;
		Complex(ll _x = 0, ll _y = 0){
			x = _x, y = _y;
		}
		Complex operator * (Complex &b){
			ll _x = (x*b.x + y*b.y % MOD *_w) % MOD;
			ll _y = (x*b.y + y*b.x) % MOD;
			return Complex(_x, _y);
		}
		Complex operator ^ (int t){
			auto ret = Complex(1, 0);
			auto bas = (*this);
			for(; t; t>>=1, bas = bas*bas)
				if(t&1) ret = ret*bas;
			return ret;
		}
	};

	// == 1：是二次剩余
	// == MOD-1：不是二次剩余
	// == 0：是 0
	ll Legendre(ll x){
		return QPow(x, (MOD-1)/2);
	}

	ll QuaRes(ll n){
		if(Legendre(n) == 0) return 0;

		mt19937 rng(time(0));
		uniform_int_distribution<> dis(0, MOD-1);
		while(1){
			ll a = dis(rng);
			_w = ((a*a - n) % MOD + MOD) % MOD;
			if(Legendre(_w) != MOD-1) continue;
			return (Complex(a, 1)^(MOD+1)/2).x;
		}
	}

	void Solve(ll d){
		// 无解
		if(Legendre(d) == MOD-1) return;
		// 解有两个，可能存在 x1 = x2 = 0 的情况
		ll x1 = QuaRes(d);
		ll x2 = MOD - x1;
	}
};

// DEBUG:
namespace BSGS{
	int BSGS(ll a,ll b,ll p){
		map<ll,int> s;
		int m=(int)ceil(sqrt(p));
		ll tmp=1;
		for(int i=0;i<m;i++,tmp=tmp*a%p)
			if(!s.count(tmp))s[tmp]=i;
		ll inv=Invert(tmp,p);tmp=b;
		for(int i=0;i<m;i++,tmp=tmp*inv%p)
			if(s.count(tmp))return i*m+s[tmp]+1;
		return -1;
	}
};

// DEBUG:
namespace ExGCD{
	void ExtendGCD(int a,int b,int &x,int &y,int &g){
		if(!b)x=1,y=0,g=a;
		else ExtendGCD(b,a%b,y,x,g),y-=x*(a/b);
	}
	// ax+by=c
	// 定义b'=b/g
	// 解集：x = x0+k*b', y = y0-k*a'
	// 最小非负解：x+ = (x0 % b'+ b') % (b'c')
	// 为啥mod b'c'，b'c'>=b'不是吗，mod b'似乎就行
};

// DEBUG:
namespace ExCRT{
	ll ExtendCRT(){
		ll a0,p0,a1,p1; bool flag=1;
		cin>>p0>>a0;
		for(int i=2;i<=n;i++){
			ll x,y,g,c;
			cin>>p1>>a1;
			if(flag){
				ExtendGCD(p0,p1,x,y,g);
				c=a1-a0;
				if(c%g){flag=0;continue;}
				x=x*(c/g)%(p1/g);
				a0+=x*p0;p0=p0*p1/g;
				a0%=p0;
			}
		}
		if(flag)return (a0%p0+p0)%p0;
		else return -1;
	}
};

// =============== 线性代数 / Linear Algebra ===============

struct LinearRecursiveFunction{
	// 如果有 x_n = a_1*x_{n-1} + ... + a_m*x_{n-m+1}
	// 那么特征多项式为 x^m = a_1*x^{m-1} + ... + a_m
	// 且数组 cpoly = reverse(a, a+m+1)
	int cpoly[N];

	void Mul(int ret[],int a[],int b[]){
		static ll c[N];
		memset(c,0,sizeof(c));
		
		// NOTE: length of a and b maybe over m
		// NOTE: so actually they should be normalized before used

		for(int i=0;i<m;i++) if(a[i])
			for(int j=0;j<m;j++) if(b[j])
				c[i+j] = (c[i+j] + 1LL*a[i]*b[j])%MOD;

		for(int i=2*m;i>=m;i--) if(c[i])
			for(int j=0;j<m;j++)
				c[i-m+j] = (c[i-m+j] + cpoly[j]*c[i])%MOD;

		for(int i=0;i<m;i++)
			ret[i]=c[i];
	}
	
	int LinearRF(ll t){
		static int ret[N],bas[N];
		memset(ret,0,sizeof(ret));
		memset(bas,0,sizeof(bas));
		ret[0]=1; bas[1]=1;
	
		for(;t;t>>=1,Mul(bas,bas,bas))
			if(t&1LL)Mul(ret,bas,ret);

		// f 是原递推线性式
		// 将求得的系数与值依次相乘即可
		ll ans=0;
		for(int i=0;i<m;i++)
			ans=(ans+ret[i]*f[i])%MOD;
	
		return ans;
	}
};

struct LBase{
	// 32位版本
	static const int S=32; 
	ui b[S];
	LBase(){
		memset(b,0,sizeof(b));
	};
	void Insert(ui x){
		for(int i=S-1;i>=0;i--)
			if(x>>i){
				if(!b[i]){
					b[i]=x; return;
				}else x^=b[i];
			}
	}
	bool Count(ui x){
		for(int i=S-1;i>=0;i--)
			if(x>>i){
				if(!b[i])return 0;
				else x^=b[i];
			}
		return 1;
	}
	// 线性基求交
	LBase operator &(LBase a){
		LBase tot=a, ret;
		for(int i=0;i<S;i++)
			if(b[i]){
				int now=b[i], det=0;
				for(int j=i;j>=0;j--)
					if(now&(1<<j)){
						if(tot.b[j]){
							now^=tot.b[j];
							det^=a.b[j];
							if(now)continue;
							ret.b[i]=det;
						}else tot.b[j]=now, a.b[j]=det;
						break;
					}
			}
		return ret;
	}
	// 线性基求并
	LBase operator |(LBase a){
		LBase ret=a;
		for(int i=0;i<S;i++)
			ret.Insert(b[i]);
		return ret;
	}
};

// =============== 计算几何 / Computational Geometry ===============

// DEBUG:
namespace 2DGeometry{
	const double EPS=1e-8;

	struct Point{
		double x,y;
		Point operator-(Point b)const{
			return (Point){x-b.x,y-b.y};
		}
		// DCmp
		int operator*(Point b)const{
			double ret=x*b.y-y*b.x;
			if(ret>EPS)return 1;
			else if(ret<-EPS)return -1;
			else return 0;
		}
	};

	bool Cmp(Point a,Point b){
		return a.x==b.x ? a.y<b.y : a.x<b.x;
	}

	const int N=100000+5;

	// may return a point or a segment
	// the end equal to the start
	// when a-b-c is collinear, b will be inserted
	void ConvexHull(vector<Point> &p,vector<Point> &ret){
		static Point s[N]; int t=0;
		sort(p.begin(),p.end(),Cmp);
		
		int n=p.size();
		for(int i=0;i<n;i++){
			while(t>1 && (s[t]-s[t-1])*(p[i]-s[t])<0)t--;
			s[++t]=p[i];
		}
		int _t=t;
		for(int i=n-2;i>=0;i--){
			while(t>_t && (s[t]-s[t-1])*(p[i]-s[t])<0)t--;
			s[++t]=p[i];
		}
		for(int i=1;i<=t;i++)
			ret.push_back(s[i]);
	}
};

// =============== 杂项 / Other ===============

struct Bignum{
	// 15*8 = 120位
	// 选8位是为了保证S*S*L不太大可以做除法
	// 但是其实也可以用个东西额外保存的，中间边乘法边取模
	const static int L=15+3, S=100000000;
	ll a[L];
	Bignum(){
		memset(a,0,sizeof(a));
	}
	void Set(int x){
		a[0]=x;
	}
	void operator+=(Bignum b){
		for(int i=0;i<L;i++)a[i]+=b.a[i];
		for(int i=0;i+1<L;i++){
			a[i+1]+=a[i]/S;
			a[i]%=S;
		}
	}
	Bignum operator*(Bignum b){
		Bignum ret;
		for(int i=0;i<L;i++)
			for(int j=0;j<=i;j++)
				ret.a[i]+=a[j]*b.a[i-j];
		for(int i=0;i+1<L;i++){
			ret.a[i+1]+=ret.a[i]/S;
			ret.a[i]%=S;
		}
		return ret;
	}
	void operator/=(int x){
		ll res=0;
		for(int i=L-1;i>=0;i--){
			res+=a[i]; a[i]=res/x;
			res=(res-a[i]*x)*S;
		}
	}
	void Print(){
		int p=L-1;
		while(p>0 && a[p]==0)p--;
		cout<<a[p];
		for(int i=p-1;i>=0;i--)
			cout<<setw(8)<<setfill('0')<<a[i];
	}
};

namespace _FastIO{
	template <typename T> inline T read(){
		T x=0, f=1; char ch=0;
		for(;!isdigit(ch);ch=getchar())
			if(ch=='-')f=-1;
		for(;isdigit(ch);ch=getchar())
			x=x*10+ch-'0';
		return x*s;
	}
	const int BUF=64+5;
	template <typename T> inline void write(T x){
		static int s[BUF]; int t=0;
		do{
			s[t++]=x%10, x/=10;
		}while(x);
		while(t)putchar(s[--t]+'0');
	}
};

// DEBUG:
// 能用__int128的时候就快得一批
namespace QMul{
	ll QMul(ll a,ll b){
		if(a>b)swap(a,b);
		ll ret=0;
		for(;b;b>>=1,(a<<=1)%=p)
			if(b&1)(ret+=a)%=p;
		return ret;
	}
};