## 图论

- 图的遍历和拓扑排序
	- 图的遍历
	- 拓扑排序
- 最短路
	- Floyd算法
		- 最小环
	- Dijstra算法
	- Bellman-Ford算法
	- SPFA算法
		- SLF优化
- 生成树
	- Prim算法
	- Kruskal算法
- 回路 
	- 欧拉回路
	- 哈密顿回路
	- 平面图（？）
- 强连通分量
- 块
	- 割点和桥
	- 点双联通分量
	- 边双联通分量- 图和树
- 路径问题
	- K短路
		- POJ2449
		- SCOI2007 K短路
	- 差分约束系统
- 生成树
	- 生成树的另类算法
	- 次小生成树
	- 特殊生成树
	- 最优比率生成树
- 2-SAT
- 欧拉公式
- 五色定理
- AOV问题
- AOE问题
- 稳定婚姻系统




## 网络流

- 网络流初步
- 定理
	- 最大匹配与最小边覆盖
	- 最大独立集与最小点覆盖
	- 最大流最小割
	- König定理：二分图最大匹配与最小点覆盖
	- 二分图最小割与最小点权覆盖
- 最大流
	- Dinic算法
		- 小凸玩矩阵
	- Sap算法
	- 有上下界的最大流
- 最小割
	- 最小割
		- 《最小割模型在信息学竞赛中的应用》 胡伯涛 
	- 平面图最小割
		- BJOI2006 狼抓兔子
		- NOI2010 海拔
		- HNOI2010 平面图判定
	- 闭合图
	- 最小点权覆盖集与最大点权独立集
		- 《两极相通——浅析最大最小定理在信息学竞赛中的应用》 周冬
	- 0/1分数规划
		- 最大密度子图
- 费用流
	- 最短路增广费用流
	- zkw-费用流
		- NOI2008 志愿者招募
	- 最小费用可行流
	- 消圈定理
		- POJ2175 Evacuation Plan
- 二分图
	- 最大匹配
		- 匈牙利算法
		- 最大流算法
		- 覆盖集和独立集
		- DAG的链与反链
		- 非二分图最大匹配
	- 带权二分图匹配
		- KM算法
		- 费用流算法




## 字符串

- Trie与AC自动机
- KMP及扩展KMP
- Manacher
- SA & SA-IS
- 后缀树
- PAM
- SAM
- 有限状态自动机
- Huffman编码
- 字符串哈希

## FFT与多项式

- FFT
	- FFT
	- NTT
	- MTT
- 多项式
	- 多项式乘法
	- 多项式除法求模
	- 多项式求逆
	- 线性递推多项式
	- BM求最短递推式
- 拉格朗日插值

- FWT

## 数论

- 素数判断
	- Robin-Miller判素数
	- Eratosthenes筛法
- 生成函数
- 离散变换
	- 同余方程
		- 大步小步
		- 扩展大步小步
		- 中国剩余定理
- 欧拉函数
	- 单个函数值
	- 欧拉函数表
- 欧几里得
	- 最大公约数
	- 扩展欧几里德
	- 不定方程求解
- 数的进制
- 群论
	- Burnside引理
	- Pólya定理
		- 循环同构染色问题
- 集合论
	- Mobius反演
- 矩阵
	- 矩阵的概念和运算
	- 矩阵乘法
	- 二分求解线性递推方程（？）
	- 多米诺骨牌棋盘覆盖方案数
	- 高斯消元
		- 异或方程组
		- 行列式
	- 特征值与特征方程
	- 矩阵的逆
	- 貌似还有更多应用
- 微积分
	- 极限思想
	- 导数
	- 积分
	- 定积分
	- 立体解析几何
- 排列组合
- 基本概念
- 二项式定理
- 康托展开
- 袋与球问题
- 排列与组合
- Ramsey定理
- 鸽笼原理
- 容斥原理
- Fibonacci数列
- Catalan数列
- Stirling数
- 差分序列（大概与sigma(i^k)(i=1->n)有关？）
- 概率论
- 简单概率
- 全概率公式
- 条件概率
- Bayes定理
- 期望值
	- 期望的线性性质
	- Codeforces 518D
	- SCOI2015 小凸想跑步
	- HNOI2015 亚瑟王
	- HNOI2013 游走
	- BZOJ3270 博物馆



## 数据结构

- 树
	- 树的遍历
	- 树的动态规划
		- 小凸玩密室
		- SHOI2014 概率充电器
		- BZOJ2152 聪聪可可
	- 树上距离问题
		- 节点到根的距离
		- 最近公共祖先
		- 节点间的距离
		- 树的直径
		- 树上不相交最长链
	- 点分治
	- Huffman树
	- 线段树
		- 小凸解密码
	- 虚数
	- 圆方树
	- 左偏树
	- 平衡树
		- Treap
		- Splay
			- 被我用非旋转Treap代替了
		- SBTree（Size Balanced Tree）
		- K-D Tree
	- 动态树
		- 树链剖分
		- Link-Cut Tree
	- 基环树
	- 树的重心
	- 树的直径
- 堆
	- 二叉堆
	- 斜堆
	- 二项堆
- 仙人掌
	- 遍历仙人掌
	- 仙人掌的直径
	- 仙人掌的动态规划
	- 动态仙人掌
- 块状链表
- 堆栈
- 队列
- 跳跃表
- 并查集
- 树状数组
- 对子树大小树分块



## 动态规划

- 多维状态动态规划
- 状态压缩动态规划
	- 递推
	- 基于连通性
- 动态规划优化
	- 降低维度
	- 优先队列
	- 单调队列
	- 矩阵加速
	- 斜率优化
	- 四边形不等式



## 计算几何

- 半平面交
- 多边形
- 多面体
- 凸包的分治法
- 旋转卡壳
	- 最远点对问题
- 增量法
- 随机增量
- 平面解析几何及其应用
- 向量
- 点积及其应用
- 叉积及其应用
- 凸多边形的交
- 离散化与扫描
- 圆反演
- 三维圆交



## 未分类

- 整体二分
- 莫队算法
- CDQ分治
- 位运算
	- 查表统计0/1个数
	- bitset及其应用
	- 更多应用
- 博弈论
	- Nim取子游戏
	- 博弈树
	- Shannon开关游戏
- HASH
	- Hash表
		- ELFhash
		- SDBM
		- BKDR
		- RK
	- 分段Hash

- 选学内容
	- 跳舞链
	- 随机调整与随机贪心
	- 爬山法与模拟退火
	- 遗传算法

	