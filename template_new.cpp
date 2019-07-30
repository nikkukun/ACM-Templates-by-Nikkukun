#include<bits/stdc++.h>
using namespace std;

typedef long long ll;
typedef unsigned int ui;
typedef unsigned long long ull;
typedef pair<int,int> pint;
typedef long double ld;

const int N=299213;
const int INF=0x3f3f3f3f;
const ll INF_LL=0x3f3f3f3f3f3f3f3f;

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

// =============== 网络流 / Network Flow ===============

namespace _MaxFlow{
	struct Dinic{
		struct Edge{int v,res;};
		vector<Edge> edg;
		vector<int> a[N*2];
		int st,ed;

		void AddEdge(int u,int v,int cap){
			edg.push_back((Edge){v,cap});
			edg.push_back((Edge){u,0});
			int siz=edg.size();
			a[u].push_back(siz-2);
			a[v].push_back(siz-1);
		}

		int dep[N*2];
		bool BFS(){
			memset(dep,-1,sizeof(dep));
			dep[st]=0; 
			queue<int> q; q.push(st);

			while(!q.empty()){
				int u=q.front(); q.pop();
				for(int i=0;i<a[u].size();i++){
					Edge& e=edg[a[u][i]];
					if(dep[e.v]==-1&&e.res>0){
						q.push(e.v), dep[e.v]=dep[u]+1;
					}
				}
			}

			return dep[ed]!=-1;
		}

		int cur[N*2];
		int DFS(int u,int minF){
			if(u==ed||minF==0)return minF;

			int tmpF,sumF=0;
			for(int& i=cur[u];i<a[u].size();i++){
				Edge& e=edg[a[u][i]];
				if( dep[e.v]==dep[u]+1 && (tmpF=DFS(e.v,min(e.res,minF)))>0 ){
					e.res-=tmpF; edg[a[u][i]^1].res+=tmpF;
					sumF+=tmpF; minF-=tmpF;
				}
				if(minF==0)break;
			}

			return sumF;
		}

		int MaxFlow(){
			int ret=0;
			while(BFS()){
				memset(cur,0,sizeof(cur));
				ret+=DFS(st,INF);
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
		for(int v=1;v<=n;v++)
			if(g[u][v] && !vst[v]){
				vst[v]=1;
				if(!lnk[v] || DFS(lnk[v],n)){
					lnk[v]=u;
					return 1;
				}
			}

		return 0;
	}

	int Match(int n){
		int ans=0;
		for(int i=1;i<=n;i++){
			memset(vst,0,sizeof(vst));
			if(DFS(i,n))ans++;
		}
		return ans;
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

namespace _AhoCorasick{
	int ch[N][C],f[N],pre[N];		// f=fail, pre=pre_end
	bool isEnd[N]; int idx;

	void Init(){
		memset(ch,0,sizeof(ch));
		memset(f,0,sizeof(f));
		memset(pre,0,sizeof(pre));
		memset(isEnd,0,sizeof(isEnd));
		idx=0;
	}

	void Build(char s[],int n){
		int o=0;
		for(int i=0;i<n;i++){
			int c=s[i];
			if(ch[o][c])o=ch[o][c];
			else o=ch[o][c]=++idx;
		}
		isEnd[o]=1;
	}

	void GetFail(){
		queue<int> q;
		for(int i=0;i<C;i++)
			if(ch[0][i])q.push(ch[0][i]);

		while(!q.empty()){
			int h=q.front(); q.pop();
			for(int i=0;i<C;i++){
				int &u=ch[h][i], j=f[h];
				if(!u){
					u=ch[j][i];
					continue;
				}
				q.push(u);
				while(j&&!ch[j][i])j=f[j];
				f[u]=ch[j][i];
				pre[u] = isEnd[f[u]]?f[u]:pre[f[u]];
			}
		}
	}

	// 查询的时候如果isEnd=1，则要不断向上找pre
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
			SAM::Insert(s[i]);
		SAM::Build();
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
			PAM::Insert(s,i);
		printf("%lld",PAM::Build());
	}
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
	const int MOD=998244353, G=3;

	ll QPow(ll bas,int t){
		ll ret=1;
		for(;t;t>>=1,bas=bas*bas%MOD)
			if(t&1)ret=ret*bas%MOD;
		return ret;
	}

	ll Inv(ll x){
		return QPow(x,MOD-2);
	}

	void NTT(int w[],int n,int op){
		static int r[N];

		for(int i=0;i<n;i++)
			r[i]=(r[i>>1]>>1)|((i&1)?n>>1:0);
		for(int i=0;i<n;i++)
			if(i<r[i])swap(w[i],w[r[i]]);
			
		for(int len=2;len<=n;len<<=1){
			int sub=len>>1;
			ll det=QPow(G,MOD-1+op*(MOD-1)/len);
			for(int l=0;l<n;l+=len){
				ll rot=1;
				for(int i=l;i<l+sub;i++){
					ll x=w[i], y=rot*w[i+sub]%MOD;
					w[i]=(x+y)%MOD;
					w[i+sub]=(x-y)%MOD;		//maybe minus
					rot=rot*det%MOD;
				}
			}
		}
		
		if(op==1)return;
		ll inv=Inv(n);
		for(int i=0;i<n;i++)
			w[i]=inv*w[i]%MOD;
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

		for(int i=0;i<n;i++){
			ll w = 0;
			w += ll(round(c[i].x/len))%MOD*D*D;
			w += ll(round(d[i].x/len))%MOD*D;
			w += ll(round(d[i].y/len))%MOD;
			ans[i] = w%MOD;
		}
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
